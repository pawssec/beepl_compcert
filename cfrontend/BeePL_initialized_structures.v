Require Import BeePL_storage_types.
(* Primitive structure initialization establishes initialized-object state.
   Both the source struct result and the reference result use the same actual
   allocation and stores. Existing pointer-valued cells are framed unchanged. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initialization_proofs BeePL_layout_proofs BeePL_structure_proofs.
Require Import BeePL_soundness_arrays BeePL_structure_copy_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_structure_object_coverage.
Require Import BeePL_initializer_coherence BeePL_heap_extents.
Require Import BeePL_initializer_frames BeePL_structure_storage_typing.
Import ListNotations.
Local Open Scope Z_scope.

Lemma structure_initializer_retype_result : forall env Gamma Sigma sid ids es t ef attr result,
  type_expr env Gamma Sigma (Sinit sid ids es t) ef t ->
  structure_result_type sid attr t ->
  structure_result_type sid attr result ->
  type_expr env Gamma Sigma (Sinit sid ids es result) ef result.
Proof.
  intros env Gamma Sigma sid ids es t ef attr result Htyped Hsource Hresult.
  pose proof (typed_structure_storage_admissible _ _ _ _ _ _ _ _ _ Htyped Hsource) as Hstorage.
  inversion Htyped; subst. eapply ty_sinit with (a := attr); eauto.
Qed.

Lemma field_initialization_load_other_block : forall ge fresh base sid ids vs ts m final,
  sem_allocate_fields ge fresh base sid ids vs ts m final ->
  forall b chunk offset, b <> fresh -> Mem.load chunk final b offset = Mem.load chunk m b offset.
Proof.
  intros ge fresh base sid ids vs ts m final Hinit.
  induction Hinit; intros old chunk offset Hneq; [reflexivity |].
  rewrite IHHinit by exact Hneq. eapply assignment_load_other_block; eauto.
Qed.

Lemma structure_initializer_located_cells :
  forall ge Sigma Sigma' L L' cells m allocated final fresh sid attr ids vs ts fs,
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Stype sid attr)) = (allocated, fresh) ->
  sem_allocate_fields ge fresh Ptrofs.zero sid ids vs ts allocated final ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m ->
  typed_memory_layout ge.(genv_cenv) Sigma' (extend_field_layout cells fresh Ptrofs.zero fs) final ->
  location_context_includes L L' ->
  memory_locations L' (extend_field_layout cells fresh Ptrofs.zero fs) final.
Proof.
  intros ge Sigma Sigma' L L' cells m allocated final fresh sid attr ids vs ts fs
    Halloc Hinit Htyped Hlocated Hfinal Hinc b ofs ty chunk Hentry actual Hread.
  destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hentry)
    as [Hold | [f [Hin [Hb [Hofs [Hty Hchunk]]]]]].
  - pose proof (Htyped _ _ _ _ Hold) as Hcell.
    assert (Hvalid : Mem.valid_block m b).
    { eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure; exact Hcell. }
    assert (Hneq : b <> fresh).
    { intro Heq. subst b. eapply Mem.fresh_block_alloc; eauto. }
    destruct Hcell as [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Hv]]]]].
    assert (Hreadv : deref_addr ty final b ofs Full v).
    { eapply deref_addr_value with (chunk := chunk) (v := cv);
        [exact Hmode | exact Hvolatile | | exact Hdecode].
      simpl. rewrite (field_initialization_load_other_block _ _ _ _ _ _ _ _ _ Hinit) by exact Hneq.
      eapply Mem.load_alloc_other; eauto. }
    assert (actual = v) by (eapply deref_full_deterministic; eauto). subst actual.
    eapply value_locations_monotone; [exact Hinc |].
    eapply Hlocated; [exact Hold |]. eapply deref_addr_value; eauto.
  - subst b ofs ty chunk. apply primitive_value_locations.
    eapply declarative_value_shape with (cenv := ge.(genv_cenv)) (Gamma := empty_context) (Sigma := Sigma').
    eapply typed_memory_cell_read_preservation;
      [apply Hfinal; apply extend_field_layout_member; exact Hin | exact Hread].
Qed.

(* This framing lemma receives initialized scalar cells from the constructive
   initializer proof; it derives all remaining object-state components. *)
Lemma structure_initializer_object_frame :
  forall p Gamma Sigma objects cells m allocated final fresh sid attr pa fs ef co,
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) (Ptrtype (Reftype (Bstruct sid attr) pa))) ef
    (Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env p.(prog_comp_env)) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (allocated, fresh) ->
  sem_allocate_fields (globalenv p) fresh Ptrofs.zero sid (map planned_field fs)
    (extract_values_exprs (planned_expressions fs)) (typeof_exprs (planned_expressions fs)) allocated final ->
  typed_memory_layout p.(prog_comp_env) Sigma (extend_field_layout cells fresh Ptrofs.zero fs) final ->
  let Sigma' := PTree.set fresh (Ptrtype (Reftype (Bstruct sid attr) pa)) Sigma in
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
  initialized_object_memory (globalenv p) Sigma' final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
    (extend_field_layout cells fresh Ptrofs.zero fs) /\
  object_type_at p.(prog_comp_env) Sigma' fresh 0 (Stype sid attr).
Proof.
  intros p Gamma Sigma objects cells m allocated final fresh sid attr pa fs ef co
    [Hobjects Hcoverage Htyped Hlocated HscalarCoherence] Hblocks Hinitializer Hco Hsize Hoffsets Halloc Hinit Hcells Sigma'.
  destruct (initialized_structure_store_extension (globalenv p) p.(prog_comp_env) Gamma Sigma
    (extend_field_layout cells fresh Ptrofs.zero fs) m allocated final fresh sid attr pa
    _ _ _ Hblocks Halloc Hinit Hcells) as [Hext [Hblocks' [Hcells' Hvalue]]].
  assert (Hnonnegative : 0 <= sizeof_type p.(prog_comp_env) (Stype sid attr)).
  { simpl. rewrite Hco. pose proof (co_sizeof_pos co). lia. }
  assert (HfreshObject : object_type_at p.(prog_comp_env) Sigma' fresh 0 (Stype sid attr)).
  { change (object_type_at p.(prog_comp_env) Sigma' fresh 0
      (stored_object_type (Ptrtype (Reftype (Bstruct sid attr) pa)))).
    apply object_type_root; [unfold Sigma'; apply PTree.gss | exact Hnonnegative]. }
  assert (Hold : aggregate_objects_valid p.(prog_comp_env) Sigma' final objects).
  { eapply aggregate_objects_valid_frame; [exact Hobjects | exact Hext | |].
    - intros b Hb. eapply field_initialization_preserves_valid_blocks; [exact Hinit |].
      eapply Mem.valid_block_alloc; eauto.
    - intros b ofs k perm Hp. eapply field_initializer_preserves_permissions; [exact Hinit |].
      eapply Mem.perm_alloc_1; eauto. }
  split; [exact Hext |]. split; [exact Hblocks' |]. split; [|exact HfreshObject]. constructor.
  - destruct Hold as [HoldTyping HoldReadable HoldAddress]. constructor;
      intros b base ty [Hentry | [Hb [Hbase Hty]]].
    + apply HoldTyping; exact Hentry.
    + subst b base ty. rewrite Ptrofs.unsigned_zero. exact HfreshObject.
    + apply HoldReadable; exact Hentry.
    + subst b base ty. eapply aggregate_readable_memory_frame.
      * eapply fresh_aggregate_readable; [reflexivity | | exact Halloc].
        split; [exact Hnonnegative |]. simpl. rewrite Hco. unfold Ptrofs.max_unsigned in Hsize. lia.
      * intros; eapply field_initialization_preserves_valid_blocks; eauto.
      * intros; eapply field_initializer_preserves_permissions; eauto.
    + eapply HoldAddress; exact Hentry.
    + subst b base ty. rewrite Ptrofs.unsigned_zero. simpl. rewrite Hco. lia.
  - eapply primitive_structure_object_coverage; eauto.
  - exact Hcells'.
  - eapply structure_initializer_located_cells with (ge := globalenv p) (sid := sid) (attr := attr);
      [exact Halloc | exact Hinit | exact Htyped | exact Hlocated | exact Hcells' |].
    eapply descriptor_heap_locations_monotone.
    + intros; apply extend_field_layout_old; assumption.
    + intros; left; assumption.
  - eapply program_primitive_structure_initializer_coherence;
      [exact Hobjects|exact Htyped|exact HscalarCoherence|exact Hinitializer|
       exact Hco|exact Hsize|exact Hoffsets|exact Halloc].
Qed.

Theorem initialized_structure_progress :
  forall Gamma Sigma objects cells p vm m sid attr pa result fs ef co,
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  exists resolved allocated final fresh Sigma',
    resolve_primitive_fields (bcomposite_composite_env p.(prog_comp_env))
      (bmembers_cmembers co.(co_members)) fs = Some resolved /\
    map planned_field resolved = map planned_field fs /\ planned_expressions resolved = planned_expressions fs /\
    Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (allocated, fresh) /\
    ssem_expr (globalenv p) p vm m (Sinit sid (map planned_field fs) (planned_expressions fs) result)
      final vm (Val (Vloc fresh Ptrofs.zero) result) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory (globalenv p) Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) /\
    type_expr p.(prog_comp_env) Gamma Sigma' (Val (Vloc fresh Ptrofs.zero) result) ef result /\
    Sigma' = PTree.set fresh (Ptrtype (Reftype (Bstruct sid attr) pa)) Sigma.
Proof.
  intros Gamma Sigma objects cells p vm m sid attr pa result fs ef co Hresult Htyped
    Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct.
  destruct (typed_primitive_structure_storage_conditions _ _ _ _ _ _ _ _ _ _ Hresult Htyped Hco) as [Hsize Hvolatile].
  assert (Hpointer : type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) (Ptrtype (Reftype (Bstruct sid attr) pa))) ef
    (Ptrtype (Reftype (Bstruct sid attr) pa))).
  { eapply structure_initializer_retype_result; [exact Htyped | |].
    - destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity].
    - right; exists pa; reflexivity. }
  pose proof (planned_initializer_effect_nil _ _ _ _ _ _ _ _ Hpointer) as Heffect. subst ef.
  destruct (resolved_primitive_structure_progress Gamma Sigma cells p vm m sid attr pa fs nil co
    Hpointer (initialized_object_cells _ _ _ _ _ Hmemory) Hco Hstruct Hsize Halign Hplain
    Hvolatile Hattrs Hdistinct) as [resolved [allocated [final [fresh [Hresolve [Halloc [Hstep Hcells]]]]]]].
  destruct (resolve_primitive_fields_spec _ _ _ _ Hresolve) as [Hnames [Hexprs [Horigins Hoffsets]]].
  destruct (completed_structure_initialization _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [_ [actual [Hactual Hinit]]].
  change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (actual, fresh)) in Hactual.
  assert (actual = allocated) by congruence. subst actual.
  assert (Hpointer' : type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field resolved) (planned_expressions resolved)
      (Ptrtype (Reftype (Bstruct sid attr) pa))) nil (Ptrtype (Reftype (Bstruct sid attr) pa))).
  { rewrite Hnames, Hexprs. exact Hpointer. }
  rewrite <- Hnames, <- Hexprs in Hinit.
  destruct (structure_initializer_object_frame p Gamma Sigma objects cells m allocated final fresh
    sid attr pa resolved nil co Hmemory Hblocks Hpointer' Hco Hsize Hoffsets Halloc Hinit Hcells)
    as [Hext [Hblocks' [Hstate Hobject]]].
  exists resolved, allocated, final, fresh, (PTree.set fresh (Ptrtype (Reftype (Bstruct sid attr) pa)) Sigma).
  split; [exact Hresolve |]. split; [exact Hnames |]. split; [exact Hexprs |]. split; [exact Halloc |]. split.
  - eapply ssem_sinit2 with (sa := attr) (allocated := allocated).
    + destruct Hresult as [-> | ->]; [left; reflexivity | right; exists pa; reflexivity].
    + apply planned_expressions_values.
    + exact Halloc.
    + rewrite <- Hnames, <- Hexprs. exact Hinit.
  - split; [exact Hext |]. split; [exact Hblocks' |]. split; [exact Hstate |]. split; [|reflexivity].
    destruct Hresult as [-> | ->].
    + apply ty_valstruct. rewrite Ptrofs.unsigned_zero. exact Hobject.
    + apply ty_valloc. apply PTree.gss.
Qed.

Print Assumptions initialized_structure_progress.

Lemma completed_structure_result_initialization :
  forall ge p vm m sid attr pa result ids es final vm' fresh,
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  ssem_expr ge p vm m (Sinit sid ids es result) final vm' (Val (Vloc fresh Ptrofs.zero) result) ->
  vm' = vm /\ exists allocated,
    Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Stype sid attr)) = (allocated, fresh) /\
    sem_allocate_fields ge fresh Ptrofs.zero sid ids (extract_values_exprs es) (typeof_exprs es) allocated final.
Proof.
  intros ge p vm m sid attr pa result ids es final vm' fresh Hshape Hstep.
  destruct Hshape as [-> | ->]; inversion Hstep; subst;
    match goal with H : structure_result_type _ _ _ |- _ =>
      destruct H as [Heq | [other Heq]]; try discriminate; inversion Heq; subst
    end;
    split; [reflexivity | |reflexivity |]; eexists; split; eassumption.
Qed.

Theorem completed_initialized_structure_preservation :
  forall Gamma Sigma objects cells p vm m sid attr pa result fs ef co final vm' fresh,
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  ssem_expr (globalenv p) p vm m (Sinit sid (map planned_field fs) (planned_expressions fs) result)
    final vm' (Val (Vloc fresh Ptrofs.zero) result) ->
  exists resolved Sigma',
    vm' = vm /\
    map planned_field resolved = map planned_field fs /\ planned_expressions resolved = planned_expressions fs /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory (globalenv p) Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) /\
    type_expr p.(prog_comp_env) Gamma Sigma' (Val (Vloc fresh Ptrofs.zero) result) ef result /\
    Sigma' = PTree.set fresh (Ptrtype (Reftype (Bstruct sid attr) pa)) Sigma.
Proof.
  intros Gamma Sigma objects cells p vm m sid attr pa result fs ef co final vm' fresh
    Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct Hactual.
  destruct (typed_primitive_structure_storage_conditions _ _ _ _ _ _ _ _ _ _ Hresult Htyped Hco) as [Hsize Hvolatile].
  destruct (initialized_structure_progress Gamma Sigma objects cells p vm m sid attr pa result fs ef co
    Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct)
    as [resolved [allocated [expected [block [Sigma' [Hresolve [Hnames [Hexprs [Halloc [Hstep
      [Hext [Hblocks' [Hstate [Hvalue Hstore]]]]]]]]]]]]]].
  destruct (completed_structure_result_initialization _ _ _ _ _ _ _ _ _ _ _ _ _ Hresult Hactual)
    as [Hvm [actual_allocated [Hactual_alloc Hactual_init]]].
  destruct (completed_structure_result_initialization _ _ _ _ _ _ _ _ _ _ _ _ _ Hresult Hstep)
    as [_ [expected_allocated [Hexpected_alloc Hexpected_init]]].
  change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (actual_allocated, fresh)) in Hactual_alloc.
  change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (expected_allocated, block)) in Hexpected_alloc.
  assert (actual_allocated = allocated /\ expected_allocated = allocated /\ fresh = block)
    as [Ha [He Hb]] by (repeat split; congruence).
  subst actual_allocated expected_allocated fresh.
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
  rewrite <- Hnames, <- Hexprs in Hactual_init, Hexpected_init.
  rewrite planned_expressions_extract, planned_expressions_types in Hactual_init, Hexpected_init.
  assert (final = expected) by (eapply planned_initialization_deterministic; eauto). subst final.
  exists resolved, Sigma'. split; [exact Hvm |]. split; [exact Hnames |]. split; [exact Hexprs |].
  split; [exact Hext |]. split; [exact Hblocks' |]. split; [exact Hstate|]. split; assumption.
Qed.
Print Assumptions completed_initialized_structure_preservation.

Require Import BeePL_packet_heap.

Lemma completed_structure_heap_extents :
  forall ge Sigma m allocated final objects cells packets fresh sid attr pa fs ids vs ts,
  heap_block_extents Sigma m objects cells packets ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Stype sid attr)) = (allocated, fresh) ->
  0 <= sizeof_type ge.(genv_cenv) (Stype sid attr) <= Ptrofs.max_unsigned ->
  sem_allocate_fields ge fresh Ptrofs.zero sid ids vs ts allocated final ->
  heap_block_extents (PTree.set fresh (Ptrtype (Reftype (Bstruct sid attr) pa)) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
    (extend_field_layout cells fresh Ptrofs.zero fs) packets.
Proof.
  intros * Hextent Halloc Hsize Hinit.
  eapply heap_extents_field_initializer; [|exact Hinit].
  eapply heap_extents_allocation; [exact Hextent|exact Halloc|exact Hsize|].
  eapply tracked_data_block_same_block_extension.
  - intros; eapply store_set_lookup_origin; eauto.
  - intros b base ty [Hold|[Hb Hrest]]; auto.
  - intros b ofs ty chunk Hin.
    destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hin)
      as [Hold|[f [Hf [Hb Hrest]]]]; auto.
  - auto.
Qed.

Theorem initialized_structure_preservation :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e',
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  packet_heap_invariant (globalenv p) Sigma m objects cells packets ->
  heap_block_extents Sigma m objects cells packets ->
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
    type_expr p.(prog_comp_env) Gamma Sigma' e' ef result /\
    runtime_locations (descriptor_heap_locations (globalenv p) cells' objects') e' /\
    (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) /\
    (forall b ofs ty, objects b ofs ty -> objects' b ofs ty) /\
    packet_heap_invariant (globalenv p) Sigma' final objects' cells' packets /\
    heap_block_extents Sigma' final objects' cells' packets.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e'
    Hresult Htyped Hmemory Hblocks Hpackets Hextents Hco Hstruct Halign Hplain Hattrs Hdistinct
    Hlocations Hstep.
  destruct (structure_initializer_step_shape _ _ _ _ _ _ _ _ _ _ _
    (planned_expressions_values fs) Hstep) as [[Hm [Hvm He]] | [actual_attr [allocated [fresh
      [Hshape [Halloc [Hinit [Hvm He]]]]]]]].
  - subst final vm' e'. exists Sigma, objects, cells.
    split; [reflexivity |]. split; [apply store_context_extends_refl |].
    split; [exact Hblocks |]. split; [exact Hmemory |]. split; [exact Htyped |].
    split; [exact Hlocations |]. split; [auto|]. split; [auto|]. split; assumption.
  - subst e'.
    destruct (completed_initialized_structure_preservation Gamma Sigma objects cells p vm m sid attr pa result
      fs ef co final vm' fresh Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain
      Hattrs Hdistinct Hstep)
      as [resolved [Sigma' [_ [Hnames [Hexprs [Hext [Hblocks' [Hstate [Hvalue Hstore]]]]]]]]].
    assert (Hpackets' : packet_heap_invariant (globalenv p) Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) packets).
    { assert (Hsame : actual_attr = attr).
      { eapply structure_result_attribute_unique; [exact Hshape|].
        destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity]. }
      subst actual_attr.
      eapply packet_heap_fresh_field_elements; [exact Hpackets|exact Hext|exact Halloc|exact Hinit| |].
      - eapply typed_primitive_structure_no_bytes_leaf; eauto.
      - intros b ofs ty chunk Hin. destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hin)
          as [Hold|[f [Hf [Hb Hrest]]]]; [left; exact Hold|right; exact Hb]. }
    assert (Hextents' : heap_block_extents Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
      (extend_field_layout cells fresh Ptrofs.zero resolved) packets).
    { rewrite Hstore. assert (Hsame : actual_attr = attr).
      { eapply structure_result_attribute_unique; [exact Hshape|].
        destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity]. }
      subst actual_attr.
      eapply completed_structure_heap_extents; [exact Hextents|exact Halloc| |exact Hinit].
      apply storage_type_size_bounds. eapply typed_structure_storage_admissible; [exact Htyped|].
      destruct Hresult as [-> | ->]; [left; reflexivity|right; exists pa; reflexivity]. }
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr)),
      (extend_field_layout cells fresh Ptrofs.zero resolved).
    split; [exact Hvm |]. split; [exact Hext |]. split; [exact Hblocks' |].
    split; [exact Hstate |]. split; [exact Hvalue |]. split.
    + destruct Hresult as [-> | ->].
      * apply aggregate_descriptor_direct; [reflexivity |]. right; auto.
      * apply aggregate_descriptor_reference; [reflexivity |]. right; auto.
    + split.
      * intros; apply extend_field_layout_old; assumption.
      * split; [intros; left; assumption|]. split; assumption.
Qed.
Print Assumptions initialized_structure_preservation.
