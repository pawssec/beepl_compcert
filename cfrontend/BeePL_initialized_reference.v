(* Aggregate references preserve initialized coverage, not only the cells that
   happened to occur in the old layout. All successor facts follow from the
   actual copy and the source object's certified leaves. *)
Require Import List ZArith AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_fresh_copy BeePL_object_coverage.
Require Import BeePL_aggregate_reference BeePL_scalar_object_layout.
Import ListNotations.

Lemma evaluated_aggregate_reference_allocation :
  forall ge p vm m basic attr src base final vm' fresh,
  is_aggregate_type (construct_type_btype basic) = true ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    final vm' (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) ->
  exists allocated, Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic))
    = (allocated, fresh).
Proof.
  intros ge p vm m basic attr src base final vm' fresh Hkind Hstep.
  inversion Hstep; subst.
  - destruct basic; simpl in Hkind; try discriminate;
      match goal with H : chunk_of_type _ = Some _ |- _ => discriminate H end.
  - eexists; eassumption.
Qed.

Lemma aggregate_reference_initialized_state :
  forall ge Sigma before objects m src base basic attr fresh final,
  initialized_object_memory ge Sigma m objects before ->
  objects src base (construct_type_btype basic) ->
  aggregate_reference_state ge Sigma before objects src base basic attr fresh final ->
  (exists allocated, Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) = (allocated, fresh)) ->
  initialized_object_memory ge
    (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
    (aggregate_reference_cells ge before src base basic fresh).
Proof.
  intros ge Sigma before objects m src base basic attr fresh final
    [Hobjects Hcoverage Htyped Hlocations HscalarCoherence] Hsource
    [Hext [Hblocks [HtypedFinal [HobjectsFinal HlocationsFinal]]]] [allocated Halloc].
  constructor; try assumption.
  - unfold aggregate_reference_cells. eapply fresh_copy_object_coverage; eauto.
  - unfold aggregate_reference_cells. eapply scalar_object_coherence_fresh_copy; eauto.
Qed.

Definition initialized_reference_state ge Sigma before objects src base basic attr fresh final : Prop :=
  let Sigma' := PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma in
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
  initialized_object_memory ge Sigma' final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
    (aggregate_reference_cells ge before src base basic fresh).

Theorem initialized_aggregate_reference_preservation :
  forall ge p vm Sigma Gamma before objects m src base basic attr final vm' e',
  initialized_object_memory ge Sigma m objects before ->
  store_blocks_valid Sigma m ->
  objects src base (construct_type_btype basic) ->
  relative_copy_alignment before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    final vm' e' ->
  exists fresh,
    vm' = vm /\ e' = Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr)) /\
    initialized_reference_state ge Sigma before objects src base basic attr fresh final /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
      e' nil (Ptrtype (Reftype basic attr)) /\
    runtime_locations
      (descriptor_heap_locations ge (aggregate_reference_cells ge before src base basic fresh)
        (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))) e'.
Proof.
  intros ge p vm Sigma Gamma before objects m src base basic attr final vm' e'
    Hinitial Hblocks Hsource Halign Hstep.
  destruct Hinitial as [Hobjects Hcoverage Htyped Hlocations HscalarCoherence] eqn:HinitialEq.
  destruct (aggregate_reference_preservation ge p vm Sigma Gamma before objects m src base basic attr
    final vm' e' Hblocks Htyped Hlocations Hobjects Hsource Halign Hstep)
    as [fresh [Hvm [He [Hstate Htype]]]].
  exists fresh. split; [exact Hvm |]. split; [exact He |]. split.
  - destruct Hstate as [Hext [HblocksFinal Hrest]] eqn:HstateEq.
    split; [exact Hext |]. split; [exact HblocksFinal |].
    apply (aggregate_reference_initialized_state ge Sigma before objects m src base basic attr fresh final).
    + constructor; assumption.
    + exact Hsource.
    + split; [exact Hext |]. split; assumption.
    + eapply evaluated_aggregate_reference_allocation.
      * exact (proj1 (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)).
      * rewrite He in Hstep. exact Hstep.
  - split; [exact Htype |]. subst e'.
    exact (proj2 (aggregate_reference_value ge Sigma Gamma before objects src base basic attr fresh
      (proj1 (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)))).
Qed.

Theorem initialized_aggregate_reference_progress :
  forall ge p vm Sigma Gamma before objects m src base basic attr,
  initialized_object_memory ge Sigma m objects before ->
  store_blocks_valid Sigma m ->
  objects src base (construct_type_btype basic) ->
  (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv))
    (transBeePL_type (construct_type_btype basic)) | Ptrofs.unsigned base)%Z ->
  relative_copy_alignment before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    initialized_reference_state ge Sigma before objects src base basic attr fresh final /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil (Ptrtype (Reftype basic attr)) /\
    runtime_locations
      (descriptor_heap_locations ge (aggregate_reference_cells ge before src base basic fresh)
        (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic)))
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))).
Proof.
  intros ge p vm Sigma Gamma before objects m src base basic attr Hinitial Hblocks Hsource Hbase Halign.
  destruct Hinitial as [Hobjects Hcoverage Htyped Hlocations HscalarCoherence] eqn:HinitialEq.
  destruct (aggregate_reference_progress ge p vm Sigma Gamma before objects m src base basic attr
    Hblocks Htyped Hlocations Hobjects Hsource Hbase Halign)
    as [final [fresh [Hstep [Hstate Htype]]]].
  exists final, fresh. split; [exact Hstep |]. split.
  - destruct Hstate as [Hext [HblocksFinal Hrest]] eqn:HstateEq.
    split; [exact Hext |]. split; [exact HblocksFinal |].
    apply (aggregate_reference_initialized_state ge Sigma before objects m src base basic attr fresh final).
    + constructor; assumption.
    + exact Hsource.
    + split; [exact Hext |]. split; assumption.
    + eapply evaluated_aggregate_reference_allocation.
      * exact (proj1 (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)).
      * exact Hstep.
  - split; [exact Htype |].
    exact (proj2 (aggregate_reference_value ge Sigma Gamma before objects src base basic attr fresh
      (proj1 (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)))).
Qed.

Print Assumptions aggregate_reference_initialized_state.
Print Assumptions initialized_aggregate_reference_preservation.
Print Assumptions initialized_aggregate_reference_progress.
