Require Import BeePL_storage_types.
(* Struct initialization preserves alias coherence. Field separation comes
   from validated composite layouts; allocation separates all old cells. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initialization_proofs BeePL_layout_proofs BeePL_structure_proofs.
Require Import BeePL_structure_copy_layout BeePL_layout_coherence.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_structures.
Require Import BeePL_structure_storage_typing BeePL_packet_heap.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_heap_extents.
Import ListNotations.
Local Open Scope Z_scope.

Lemma separated_field_members : forall fs base f g,
  field_plans_separated base fs -> In f fs -> In g fs ->
  f = g \/ planned_end base f <= planned_start base g \/ planned_end base g <= planned_start base f.
Proof.
  induction fs as [|head rest IH]; intros base f g Hsep Hf Hg; [contradiction |].
  destruct Hsep as [Hhead Hrest]. destruct Hf as [<- | Hf]; destruct Hg as [<- | Hg].
  - left; reflexivity.
  - right; apply Hhead; exact Hg.
  - right. destruct (Hhead f Hf); auto.
  - eapply IH; eauto.
Qed.

Lemma fresh_separated_field_layout_coherent : forall cells fresh base fs,
  coherent_layout cells ->
  (forall ofs ty chunk, ~ cells fresh ofs ty chunk) ->
  field_plans_separated base fs ->
  coherent_layout (extend_field_layout cells fresh base fs).
Proof.
  intros cells fresh base fs Hcoherent Hfresh Hsep b ofs ty chunk Hentry old off t ch Hold.
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hentry)
    as [HentryOld | [f [Hf [Hb [Hofs [Hty Hchunk]]]]]];
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hold)
    as [HoldOld | [g [Hg [Holdb [Hoff [Ht Hch]]]]]].
  - eapply Hcoherent; eauto.
  - subst old off t ch. right; left. intro Heq. subst b. eapply Hfresh; eauto.
  - subst b ofs ty chunk. right; left. intro Heq. subst old. eapply Hfresh; eauto.
  - subst b ofs ty chunk old off t ch.
    destruct (separated_field_members _ _ _ _ Hsep Hf Hg) as [Heq | Hapart].
    + subst g. left; repeat split; reflexivity.
    + right; right. exact Hapart.
Qed.

Theorem allocated_primitive_structure_layout_coherent :
  forall ge cenv Sigma cells m allocated fresh size sid co fs,
  coherent_layout cells -> typed_memory_layout cenv Sigma cells m ->
  Mem.alloc m 0 size = (allocated, fresh) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env ge.(genv_cenv)) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_plan_valid ge sid f) ->
  (forall f, In f fs -> field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
    OK (transBeePL_type (Vtype (planned_type f)))) ->
  NoDup (map planned_field fs) ->
  coherent_layout (extend_field_layout cells fresh Ptrofs.zero fs).
Proof.
  intros ge cenv Sigma cells m allocated fresh size sid co fs Hcoherent Hmemory Halloc
    Hco Hconsistent Hstruct Hsize Hplans Htypes Hnames.
  apply fresh_separated_field_layout_coherent; [exact Hcoherent | |].
  - intros ofs ty chunk Hcell. eapply Mem.fresh_block_alloc; [exact Halloc |].
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. apply Hmemory; exact Hcell.
  - eapply primitive_field_plan_separation; eauto.
Qed.

Theorem coherent_initialized_structure_preservation :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e',
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  packet_heap_invariant (globalenv p) Sigma m objects cells packets ->
  heap_block_extents Sigma m objects cells packets ->
  coherent_layout cells ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  runtime_locations (descriptor_heap_locations (globalenv p) cells objects)
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ->
  ssem_expr (globalenv p) p vm m
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) final vm' e' ->
  exists Sigma' objects' cells',
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory (globalenv p) Sigma' final objects' cells' /\
    coherent_layout cells' /\ type_expr p.(prog_comp_env) Gamma Sigma' e' ef result /\
    runtime_locations (descriptor_heap_locations (globalenv p) cells' objects') e' /\
    (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) /\
    (forall b ofs ty, objects b ofs ty -> objects' b ofs ty) /\
    packet_heap_invariant (globalenv p) Sigma' final objects' cells' packets /\
    heap_block_extents Sigma' final objects' cells' packets.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e'
    Hresult Htyped Hmemory Hblocks Hpackets Hextents Hcoherent Hco Hstruct Halign Hplain Hattrs Hdistinct
    Hlocations Hactual.
  destruct (typed_primitive_structure_storage_conditions _ _ _ _ _ _ _ _ _ _ Hresult Htyped Hco) as [Hsize Hvolatile].
  destruct (structure_initializer_step_shape _ _ _ _ _ _ _ _ _ _ _
    (planned_expressions_values fs) Hactual) as [[Hm [Hvm He]] | [actual_attr [actual_memory [actual_block
      [Hshape [Hactual_alloc [Hactual_init [Hvm He]]]]]]]].
  - subst final vm' e'. exists Sigma, objects, cells.
    split; [reflexivity |]. split; [apply store_context_extends_refl |]. split; [exact Hblocks |].
    split; [exact Hmemory |]. split; [exact Hcoherent |]. split; [exact Htyped |].
    split; [exact Hlocations |]. split; [auto|]. split; [auto|]. split; assumption.
  - subst e'.
    destruct (initialized_structure_progress Gamma Sigma objects cells p vm m sid attr pa result fs ef co
      Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct)
      as [resolved [allocated [expected [fresh [Sigma' [Hresolve [Hnames [Hexprs [Halloc [Hstep
        [Hext [Hblocks' [Hstate [Hvalue Hstore]]]]]]]]]]]]]].
    destruct (completed_structure_result_initialization _ _ _ _ _ _ _ _ _ _ _ _ _ Hresult Hactual)
      as [_ [actual_allocated [HallocA HinitA]]].
    destruct (completed_structure_result_initialization _ _ _ _ _ _ _ _ _ _ _ _ _ Hresult Hstep)
      as [_ [expected_allocated [HallocE HinitE]]].
    change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (actual_allocated, actual_block)) in HallocA.
    change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (expected_allocated, fresh)) in HallocE.
    assert (actual_allocated = allocated /\ expected_allocated = allocated /\ actual_block = fresh)
      as [Ha [He Hb]] by (repeat split; congruence).
    subst actual_allocated expected_allocated actual_block.
    destruct (resolve_primitive_fields_spec _ _ _ _ Hresolve) as [_ [_ [Horigins Hoffsets]]].
    assert (Hpointer : type_expr p.(prog_comp_env) Gamma Sigma
      (Sinit sid (map planned_field resolved) (planned_expressions resolved)
        (Ptrtype (Reftype (Bstruct sid attr) pa))) ef (Ptrtype (Reftype (Bstruct sid attr) pa))).
    { rewrite Hnames, Hexprs. eapply structure_initializer_retype_result; [exact Htyped | |].
      - destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity].
      -
      right; exists pa; reflexivity. }
    assert (Hvolatile' : forall f, In f resolved -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false).
    { intros f Hin. destruct (Horigins f Hin) as [old [Hold Hty]]. rewrite Hty. apply Hvolatile; exact Hold. }
    pose proof (typed_structure_plan_facts _ _ _ _ _ _ _ _ _ Hpointer Hco Hvolatile') as Hfacts.
    assert (Hplans : forall f, In f resolved -> field_plan_valid (globalenv p) sid f).
    { intros f Hin. exists co. split; [exact Hco |]. split; [apply Hoffsets; exact Hin |].
      split; [exact (proj1 (Hfacts f Hin)) | apply Hvolatile'; exact Hin]. }
    rewrite <- Hnames, <- Hexprs in HinitA, HinitE.
    rewrite planned_expressions_extract, planned_expressions_types in HinitA, HinitE.
    assert (final = expected) by (eapply planned_initialization_deterministic; eauto). subst final.
    assert (Hcoherent' : coherent_layout (extend_field_layout cells fresh Ptrofs.zero resolved)).
    { eapply allocated_primitive_structure_layout_coherent with (ge := globalenv p) (sid := sid) (co := co);
        [exact Hcoherent | exact (initialized_object_cells _ _ _ _ _ Hmemory) | exact Halloc |
         exact Hco | | exact Hstruct | exact Hsize | exact Hplans | |].
      - exact (program_composites_consistent p sid co Hco).
      - intros f Hin. exact (proj2 (Hfacts f Hin)).
      - rewrite Hnames. exact Hdistinct. }
    assert (Hpackets' : packet_heap_invariant (globalenv p) Sigma' expected
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) packets).
    { eapply packet_heap_fresh_field_elements; [exact Hpackets|exact Hext|exact Halloc|exact HinitA| |].
      - eapply typed_primitive_structure_no_bytes_leaf; eauto.
      - intros b ofs ty chunk Hin. destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hin)
          as [Hold|[f [Hf [Hb Hrest]]]]; [left; exact Hold|right; exact Hb]. }
    assert (Hextents' : heap_block_extents Sigma' expected
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) packets).
    { rewrite Hstore. eapply completed_structure_heap_extents with (ge := globalenv p);
        [exact Hextents|exact Halloc| |exact HinitA].
      apply storage_type_size_bounds. eapply typed_structure_storage_admissible; [exact Htyped|].
      destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity]. }
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr)),
      (extend_field_layout cells fresh Ptrofs.zero resolved).
    split; [exact Hvm |]. split; [exact Hext |]. split; [exact Hblocks' |]. split; [exact Hstate |].
    split; [exact Hcoherent' |]. split; [exact Hvalue |]. split.
    + destruct Hresult as [-> | ->].
      * apply aggregate_descriptor_direct; [reflexivity |]. right; auto.
      * apply aggregate_descriptor_reference; [reflexivity |]. right; auto.
    + split.
      * intros; apply extend_field_layout_old; assumption.
      * split; [intros; left; assumption|]. split; assumption.
Qed.
Print Assumptions allocated_primitive_structure_layout_coherent.
Print Assumptions coherent_initialized_structure_preservation.

Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_callable_variables.

Theorem coherent_structure_configuration_preservation :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e',
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  ssem_expr (globalenv p) p vm m
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) final vm' e' ->
  exists Sigma' objects' cells',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets e' ef result.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e'
    [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes] Hcoherent]
    Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct Hstep.
  destruct (coherent_initialized_structure_preservation Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co
    final vm' e' Hresult Htyped Hmemory Hblocks Hpackets Hextents Hcoherent Hco Hstruct Halign Hplain Hattrs Hdistinct
    ltac:(eapply typed_planned_structure_locations; exact Htyped) Hstep)
    as [Sigma' [objects' [cells' [Hvm [Hext [Hblocks' [Hmemory' [Hcoherent' [Htyped' [Hlocations' [Hcells [Hobjects [Hpackets' Hextents']]]]]]]]]]]]].
  exists Sigma', objects', cells'. split; [constructor; auto |]. split; [|exact Hcoherent']. constructor.
  - constructor; try assumption. subst vm'. eapply packet_variable_layout_extend; eauto.
  - exact Htyped'.
  - eapply runtime_locations_monotone; [apply packet_descriptor_embedding|exact Hlocations'].
  - destruct (structure_initializer_step_shape _ _ _ _ _ _ _ _ _ _ _
      (planned_expressions_values fs) Hstep) as [[Hm [Hvm0 He]] | [actual_attr [allocated [fresh
        [Hshape [Halloc [Hinit [Hvm0 He]]]]]]]].
    + subst e'. eapply initialized_runtime_frames_evolve; eauto.
    + subst e'. exact I.
Qed.

Theorem coherent_structure_configuration_progress :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  exists final fresh Sigma' objects' cells',
    ssem_expr (globalenv p) p vm m
      (Sinit sid (map planned_field fs) (planned_expressions fs) result) final vm
      (Val (Vloc fresh Ptrofs.zero) result) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm final objects' cells' packets
      (Val (Vloc fresh Ptrofs.zero) result) ef result.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co Hconfig
    Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct.
  destruct Hconfig as [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes] Hcoherent].
  destruct (initialized_structure_progress Gamma Sigma objects cells p vm m sid attr pa result fs ef co
    Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct)
    as [resolved [allocated [final [fresh [allocatedStore [Hresolve [Hnames [Hexprs [Halloc [Hstep Hrest]]]]]]]]]].
  assert (Hconfig : coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result).
  { split; [|exact Hcoherent]. constructor; [constructor; assumption |assumption |assumption |assumption]. }
  destruct (coherent_structure_configuration_preservation Gamma Sigma objects cells packets p vm m sid attr pa result
    fs ef co final vm _ Hconfig Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct Hstep)
    as [Sigma' [objects' [cells' [Hevolution Hfinal]]]].
  exists final, fresh, Sigma', objects', cells'. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions coherent_structure_configuration_preservation.
Print Assumptions coherent_structure_configuration_progress.
