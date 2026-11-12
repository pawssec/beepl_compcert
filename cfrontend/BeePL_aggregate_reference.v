(* Fresh aggregate references copy initialized leaves and extend both store
   typing and object identity. The source alignment obligations come from
   aggregate layout, not from assumed successor-state validity. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy BeePL_fresh_copy.
Require Import BeePL_fresh_aggregate_memory.
Require Import BeePL_layout_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma basic_reference_copy_size : forall ge basic,
  aggregate_copy_size ge (construct_type_btype basic) =
    sizeof_type ge.(genv_cenv) (construct_type_btype basic).
Proof. reflexivity.
Qed.

Definition aggregate_reference_cells ge before src base basic fresh :=
  fresh_copy_layout before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) fresh.

Definition aggregate_reference_state ge Sigma before objects src base basic attr fresh final : Prop :=
  let Sigma' := PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma in
  let cells' := aggregate_reference_cells ge before src base basic fresh in
  let objects' := add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic) in
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
  typed_memory_layout ge.(genv_cenv) Sigma' cells' final /\
  aggregate_objects_valid ge.(genv_cenv) Sigma' final objects' /\
  memory_locations (descriptor_heap_locations ge cells' objects') cells' final.

Lemma aggregate_reference_value : forall ge Sigma Gamma before objects src base basic attr fresh,
  is_aggregate_type (construct_type_btype basic) = true ->
  type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
    (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil
    (Ptrtype (Reftype basic attr)) /\
  runtime_locations
    (descriptor_heap_locations ge (aggregate_reference_cells ge before src base basic fresh)
      (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic)))
    (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))).
Proof.
  intros. split; [constructor; apply PTree.gss |].
  apply aggregate_descriptor_reference; [assumption |]. right; auto.
Qed.

Theorem fresh_aggregate_assignment_state :
  forall ge Sigma before objects m allocated final src base basic attr fresh,
  store_blocks_valid Sigma m ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations (descriptor_heap_locations ge before objects) before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects src base (construct_type_btype basic) ->
  relative_copy_alignment before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) = (allocated, fresh) ->
  assign_addr ge (construct_type_btype basic) allocated fresh Ptrofs.zero Full
    (Vloc src base) final (Vloc src base) ->
  aggregate_reference_state ge Sigma before objects src base basic attr fresh final.
Proof.
  intros ge Sigma before objects m allocated final src base basic attr fresh
    Hblocks Htyped Hlocated Hobjects Hsource Halign Halloc Hassign.
  pose proof (basic_reference_copy_size ge basic) as Hsizes.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource) as Hreadable.
  destruct Hreadable as [Hkind [Hnonnegative [Hextent [HsrcBlock Hread]]]].
  assert (Hbound : 0 <= sizeof_type ge.(genv_cenv) (construct_type_btype basic) <= Ptrofs.modulus).
  { pose proof (Ptrofs.unsigned_range base). lia. }
  destruct (fresh_reference_aggregate_descriptors ge.(genv_cenv) Sigma m objects basic attr
    allocated fresh Hobjects Hblocks Hkind
    ltac:(pose proof (aggregate_object_address_bound _ _ _ _ Hobjects _ _ _ Hsource);
      pose proof (Ptrofs.unsigned_range base); lia) Halloc)
    as [Hext [HblocksAllocated HobjectsAllocated]].
  destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign)
    as [bytes [Hbytes Hstore]].
  rewrite Hsizes in Hbytes. rewrite Ptrofs.unsigned_zero in Hstore.
  destruct (fresh_copy_preserves_cells ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge before objects) before m allocated final fresh src
    (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) bytes
    Htyped Hlocated Halloc Hbound Halign Hbytes Hstore) as [HtypedFinal HlocatedFinal].
  unfold aggregate_reference_state, aggregate_reference_cells.
  split; [exact Hext |]. split.
  - intros block ty Hentry. eapply Mem.storebytes_valid_block_1; [exact Hstore |].
    apply HblocksAllocated with (t := ty); exact Hentry.
  - split.
    + eapply typed_memory_layout_context_extension; eauto.
    + split; [eapply aggregate_objects_valid_storebytes; eauto |].
      intros block ofs ty chunk Hentry v Hvalue.
      eapply value_locations_monotone with (L := descriptor_heap_locations ge before objects).
      * eapply descriptor_heap_locations_monotone.
        -- intros. apply fresh_copy_layout_extends; assumption.
        -- intros. left; assumption.
      * eapply HlocatedFinal; eauto.
Qed.

Theorem aggregate_reference_progress :
  forall ge p vm Sigma Gamma before objects m src base basic attr,
  store_blocks_valid Sigma m ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations (descriptor_heap_locations ge before objects) before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects src base (construct_type_btype basic) ->
  (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv))
    (transBeePL_type (construct_type_btype basic)) | Ptrofs.unsigned base) ->
  relative_copy_alignment before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    aggregate_reference_state ge Sigma before objects src base basic attr fresh final /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil (Ptrtype (Reftype basic attr)).
Proof.
  intros ge p vm Sigma Gamma before objects m src base basic attr
    Hblocks Htyped Hlocated Hobjects Hsource HsourceAlign Halign.
  pose proof (basic_reference_copy_size ge basic) as Hsizes.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource) as Hreadable.
  destruct (Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)))
    as [allocated fresh] eqn:Halloc.
  pose proof (fresh_aggregate_copy_ready ge m allocated src base fresh (construct_type_btype basic)
    Halloc Hreadable HsourceAlign) as Hready.
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hready) as [final Hassign].
  exists final, fresh. split.
  - eapply ssem_ref_aggregate; [exact (proj1 Hreadable) | exact Halloc | exact Hassign].
  - split; [eapply fresh_aggregate_assignment_state; eauto |]. constructor. apply PTree.gss.
Qed.

Theorem aggregate_reference_preservation :
  forall ge p vm Sigma Gamma before objects m src base basic attr final vm' e',
  store_blocks_valid Sigma m ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations (descriptor_heap_locations ge before objects) before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects src base (construct_type_btype basic) ->
  relative_copy_alignment before src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    final vm' e' ->
  exists fresh,
    vm' = vm /\ e' = Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr)) /\
    aggregate_reference_state ge Sigma before objects src base basic attr fresh final /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
      e' nil (Ptrtype (Reftype basic attr)).
Proof.
  intros ge p vm Sigma Gamma before objects m src base basic attr final vm' e'
    Hblocks Htyped Hlocated Hobjects Hsource Halign Hstep.
  pose proof (basic_reference_copy_size ge basic) as Hsizes.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource) as Hreadable.
  destruct Hreadable as [Hkind Hrest]. inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - destruct basic; simpl in Hkind; try discriminate;
      match goal with H : chunk_of_type _ = Some _ |- _ => discriminate H end.
  - eexists. split; [reflexivity |]. split; [reflexivity |]. split.
    + eapply fresh_aggregate_assignment_state; eauto.
    + constructor. apply PTree.gss.
Qed.

Print Assumptions fresh_aggregate_assignment_state.
Print Assumptions aggregate_reference_progress.
Print Assumptions aggregate_reference_preservation.

Corollary zero_based_aggregate_reference_progress :
  forall ge p vm Sigma Gamma before objects m src basic attr,
  store_blocks_valid Sigma m ->
  typed_memory_layout ge.(genv_cenv) Sigma before m ->
  memory_locations (descriptor_heap_locations ge before objects) before m ->
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects src Ptrofs.zero (construct_type_btype basic) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val (Vloc src Ptrofs.zero) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    aggregate_reference_state ge Sigma before objects src Ptrofs.zero basic attr fresh final /\
    type_expr ge.(genv_cenv) Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil (Ptrtype (Reftype basic attr)).
Proof.
  intros. eapply aggregate_reference_progress; eauto.
  - rewrite Ptrofs.unsigned_zero. exists 0; lia.
  - rewrite Ptrofs.unsigned_zero. eapply zero_based_copy_alignment; eauto.
Qed.

Print Assumptions zero_based_aggregate_reference_progress.
