(* Actual primitive-array initialization establishes initialized-object
   coverage. Existing objects and pointer-valued cells are framed across it. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_array_proofs BeePL_soundness_arrays BeePL_aggregate_memory.
Require Import BeePL_object_coverage BeePL_array_object_coverage BeePL_initializer_frames.
Require Import BeePL_array_storage_typing BeePL_initializer_coherence.
Import ListNotations.
Local Open Scope Z_scope.

Lemma array_initializer_located_cells :
  forall ge Sigma Sigma' L L' cells arr pt len attr vs vm m vm' final bookkeeping fresh,
  sem_array_init ge Sigma arr (Atype (Vtype pt) len attr) vs vm m vm' final bookkeeping ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m ->
  typed_memory_layout ge.(genv_cenv) Sigma' (extend_array_layout cells fresh pt (length vs)) final ->
  location_context_includes L L' ->
  memory_locations L' (extend_array_layout cells fresh pt (length vs)) final.
Proof.
  intros ge Sigma Sigma' L L' cells arr pt len attr vs vm m vm' final bookkeeping fresh
    Hinit Htyped Hlocated Hfinal Hinc b ofs ty chunk Hentry actual Hread.
  destruct Hentry as [Hold | [i [Hi [Hb [Hofs [Hty Hchunk]]]]]].
  - pose proof (Htyped _ _ _ _ Hold) as Hcell.
    assert (Hvalid : Mem.valid_block m b).
    { eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure; exact Hcell. }
    destruct Hcell as [Hmode Hvolatile Hpermission [cv [v [Hload [Hdecode Hv]]]]].
    assert (Hreadv : deref_addr ty final b ofs Full v).
    { eapply deref_addr_value with (chunk := chunk) (v := cv);
        [exact Hmode | exact Hvolatile | | exact Hdecode].
      simpl. erewrite array_initialization_load_old_block; eauto. }
    assert (actual = v) by (eapply deref_full_deterministic; eauto).
    subst actual. eapply value_locations_monotone; [exact Hinc |].
    eapply Hlocated; [exact Hold |]. eapply deref_addr_value; eauto.
  - subst b ofs ty chunk. apply primitive_value_locations.
    eapply declarative_value_shape with (Gamma := empty_context).
    eapply typed_memory_cell_read_preservation;
      [apply Hfinal; right; exists i; repeat split; auto | exact Hread].
Qed.

Theorem primitive_array_initialized_objects :
  forall ge Gamma Sigma objects cells arr pt len attr vs vm m vm' final Sigma',
  sem_array_init ge Sigma arr (Atype (Vtype pt) len attr) vs vm m vm' final Sigma' ->
  initialized_object_memory ge Sigma m objects cells -> store_blocks_valid Sigma m ->
  Forall (fun v => typeof_value v (Vtype pt)) vs ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  exists fresh,
    PTree.get arr vm' = Some (fresh, Atype (Vtype pt) len attr) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length vs)) /\
    type_expr ge.(genv_cenv) Gamma Sigma'
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) nil (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells arr pt len attr vs vm m vm' final Sigma'
    Hinit [Hobjects Hcoverage Htyped Hlocated HscalarCoherence] Hblocks Hvalues Hvolatile Hbound.
  destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hinit)
    as [allocated [fresh [Halloc [Hlookup [Hhelper [Hlen [HS Hvm]]]]]]].
  destruct (array_initialization_store_typing ge ge.(genv_cenv) Gamma Sigma arr (Vtype pt)
    len attr vs vm m vm' final Sigma' Hinit Hblocks (primitive_array_size_nonnegative _ _ _ _))
    as [actual [Hlookup' [Hext [Hblocks' Hvalue]]]].
  assert (actual = fresh) by congruence. subst actual.
  destruct (primitive_array_initialization_memory_layout ge Sigma arr pt len attr vs vm m
    vm' final Sigma' ge.(genv_cenv) Sigma cells Hinit Hvalues Hvolatile
    ltac:(rewrite <- Hlen; exact Hbound) Htyped) as [actual [Hlookup'' Hcells]].
  assert (actual = fresh) by congruence. subst actual.
  assert (Hcells' : typed_memory_layout ge.(genv_cenv) Sigma'
    (extend_array_layout cells fresh pt (length vs)) final).
  { eapply typed_memory_layout_context_extension; eauto. }
  assert (HoldObjects : aggregate_objects_valid ge.(genv_cenv) Sigma' final objects).
  { eapply array_initialization_preserves_descriptors; eauto. }
  assert (HfreshReadable : aggregate_readable ge.(genv_cenv) final fresh Ptrofs.zero
    (Atype (Vtype pt) len attr)).
  { destruct (allocated_array_helper_full_range _ _ _ _ _ _ _ _ Halloc Hhelper) as [Hvalid Hrange].
    unfold aggregate_readable. rewrite Ptrofs.unsigned_zero.
    split; [reflexivity |]. split; [apply primitive_array_size_nonnegative |]. split.
    - simpl. rewrite Z.max_r by (rewrite Hlen; lia). unfold Ptrofs.max_unsigned in Hbound. lia.
    - split; [exact Hvalid |]. intros offset Hin.
      eapply Mem.perm_implies; [apply Hrange; lia | constructor]. }
  exists fresh. split; [exact Hlookup |]. split; [exact Hext |]. split; [exact Hblocks' |].
  split; [|exact Hvalue]. constructor.
  - destruct HoldObjects as [HoldTyping HoldReadable HoldAddress]. constructor;
      intros b base ty [Hold | [Hb [Hbase Hty]]].
    + apply HoldTyping; exact Hold.
    + subst b base ty. eapply array_location_typing_entry; exact Hvalue.
    + apply HoldReadable; exact Hold.
    + subst b base ty. exact HfreshReadable.
    + eapply HoldAddress; exact Hold.
    + subst b base ty. rewrite Ptrofs.unsigned_zero. simpl.
      rewrite Z.max_r by (rewrite Hlen; lia). lia.
  - rewrite Hlen. apply primitive_array_descriptor_coverage; exact Hcoverage.
  - exact Hcells'.
  - eapply array_initializer_located_cells; [exact Hinit | exact Htyped | exact Hlocated | exact Hcells' |].
    eapply descriptor_heap_locations_monotone.
    + intros; left; assumption.
    + intros; left; assumption.
  - rewrite Hlen. eapply primitive_array_initializer_coherence;
      [exact Hobjects|exact Htyped|exact HscalarCoherence| |].
    + rewrite <- Hlen. exact Halloc.
    + rewrite <- Hlen. exact Hbound.
Qed.

Theorem completed_initialized_array_preservation :
  forall ge Gamma Sigma objects cells p vm m arr pt len attr es ef final vm' fresh,
  type_expr ge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  ssem_expr ge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm'
    (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ->
  exists Sigma', Sigma' = PTree.set fresh (Atype (Vtype pt) len attr) Sigma /\
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) /\
    type_expr ge.(genv_cenv) Gamma Sigma'
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells p vm m arr pt len attr es ef final vm' fresh
    Htyped Hvalues Hblocks Hmemory Hstep.
  destruct (typed_primitive_array_storage_conditions _ _ _ _ _ _ _ _ _ Htyped) as [Hvolatile Hbound].
  destruct (typed_primitive_array_arguments _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hlength [Hshapes Heffect]]. subst ef.
  inversion Hstep; subst.
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_rebase _ _ _ _ _ _ _ _ _ _ Hinit Sigma)
      as [postSigma Hreal]
  end.
  destruct (primitive_array_initialized_objects ge Gamma Sigma objects cells arr pt _ attr
    (extract_values_exprs es) _ m _ final postSigma Hreal Hmemory Hblocks Hshapes Hvolatile Hbound)
    as [actual [Hlookup [Hext [Hblocks' [Hstate Hvalue]]]]].
  assert (actual = fresh) by congruence. subst actual.
  rewrite extracted_value_arguments_length in Hstate by exact Hvalues.
  destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hreal)
    as [allocated [actual [Ha [Hlookup' [Hhelper [Hlen [HS Hvm]]]]]]].
  assert (actual=fresh) by congruence. subst actual.
  exists postSigma. split; [exact HS|]. split; [reflexivity |]. split; [exact Hext |].
  split; [exact Hblocks' |]. split.
  - rewrite extracted_value_arguments_length by exact Hvalues. exact Hstate.
  - exact Hvalue.
Qed.

Theorem initialized_array_progress :
  forall ge Gamma Sigma objects cells p vm m arr pt len attr es ef,
  type_expr ge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  exists final fresh Sigma',
    ssem_expr ge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) /\
    type_expr ge.(genv_cenv) Gamma Sigma'
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells p vm m arr pt len attr es ef
    Htyped Hvalues Hblocks Hmemory.
  destruct (typed_primitive_array_storage_conditions _ _ _ _ _ _ _ _ _ Htyped) as [Hvolatile Hbound].
  destruct (source_primitive_array_progress ge ge.(genv_cenv) Gamma Sigma cells p vm m
    arr pt len attr es ef Htyped Hvalues Hvolatile Hbound Hblocks
    (initialized_object_cells _ _ _ _ _ Hmemory)) as [vm' [final [oldSigma [fresh [Hstep Hrest]]]]].
  destruct (completed_initialized_array_preservation ge Gamma Sigma objects cells p vm m arr pt len attr
    es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep)
    as [Sigma' [HSigma [Hvm [Hext [Hblocks' [Hstate Hvalue]]]]]].
  subst vm'. exists final, fresh, Sigma'. split; [exact Hstep |]. split; [exact Hext |].
  split; [exact Hblocks' |]. split; assumption.
Qed.

Print Assumptions primitive_array_initialized_objects.
Print Assumptions completed_initialized_array_preservation.
Print Assumptions initialized_array_progress.

(* The list semantics may also take an identity step over value arguments.
   This statement covers every actual successor, including that case. *)
Theorem initialized_array_preservation :
  forall ge Gamma Sigma objects cells p vm m arr pt len attr es ef final vm' e',
  type_expr ge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  runtime_locations (descriptor_heap_locations ge cells objects)
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ->
  ssem_expr ge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm' e' ->
  exists Sigma' objects' cells',
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final objects' cells' /\
    type_expr ge.(genv_cenv) Gamma Sigma' e' ef (Atype (Vtype pt) len attr) /\
    runtime_locations (descriptor_heap_locations ge cells' objects') e' /\
    (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) /\
    (forall b ofs ty, objects b ofs ty -> objects' b ofs ty).
Proof.
  intros ge Gamma Sigma objects cells p vm m arr pt len attr es ef final vm' e'
    Htyped Hvalues Hblocks Hmemory Hlocations Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]].
  - subst final vm' e'. exists Sigma, objects, cells.
    split; [reflexivity |]. split; [apply store_context_extends_refl |].
    split; [exact Hblocks |]. split; [exact Hmemory |]. split; [exact Htyped |].
    split; [exact Hlocations |]. split; auto.
  - subst e'.
    destruct (completed_initialized_array_preservation ge Gamma Sigma objects cells p vm m
      arr pt len attr es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep)
      as [Sigma' [HSigma [Hvm [Hext [Hblocks' [Hstate Hvalue]]]]]].
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr)),
      (extend_array_layout cells fresh pt (length es)).
    split; [exact Hvm |]. split; [exact Hext |]. split; [exact Hblocks' |].
    split; [exact Hstate |]. split; [exact Hvalue |]. split.
    + apply aggregate_descriptor_direct; [reflexivity |]. right; auto.
    + split; intros; left; assumption.
Qed.

Print Assumptions initialized_array_preservation.
