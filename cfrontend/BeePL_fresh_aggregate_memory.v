(* Fresh aggregate destinations: permissions, object descriptors and store
   extension are established before copying, without assuming final contents. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy.
Local Open Scope Z_scope.

Theorem fresh_aggregate_copy_ready : forall ge m allocated src base fresh ty,
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) ty) = (allocated, fresh) ->
  aggregate_readable ge.(genv_cenv) m src base ty ->
  (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type ty)
    | Ptrofs.unsigned base) ->
  aggregate_copy_ready ge allocated ty src base fresh Ptrofs.zero.
Proof.
  intros ge m allocated src base fresh ty Halloc
    [Hkind [Hsize [Hbound [Hsource Hread]]]] Halign.
  assert (Hsizes : aggregate_copy_size ge ty = sizeof_type ge.(genv_cenv) ty) by reflexivity.
  constructor; try assumption.
  - eapply Mem.valid_block_alloc; eauto.
  - eapply Mem.valid_new_block; eauto.
  - rewrite Ptrofs.unsigned_zero, Hsizes.
    pose proof (Ptrofs.unsigned_range base). lia.
  - rewrite Ptrofs.unsigned_zero. exists 0. lia.
  - left. intro Heq. subst src. eapply Mem.fresh_block_alloc; eauto.
  - rewrite Hsizes. intros offset Hin. eapply Mem.perm_alloc_1; eauto.
  - rewrite Ptrofs.unsigned_zero, Hsizes. intros offset Hin.
    eapply Mem.perm_alloc_2; eauto.
Qed.

Theorem fresh_reference_aggregate_descriptors :
  forall cenv Sigma m objects basic attr allocated fresh,
  aggregate_objects_valid cenv Sigma m objects ->
  store_blocks_valid Sigma m ->
  is_aggregate_type (construct_type_btype basic) = true ->
  0 <= sizeof_type cenv (construct_type_btype basic) <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 (sizeof_type cenv (construct_type_btype basic)) = (allocated, fresh) ->
  store_context_extends Sigma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) /\
  store_blocks_valid (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) allocated /\
  aggregate_objects_valid cenv (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
    allocated (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic)).
Proof.
  intros cenv Sigma m objects basic attr allocated fresh Hobjects Hblocks Hkind Hsize Halloc.
  assert (Hmissing : PTree.get fresh Sigma = None).
  { destruct (PTree.get fresh Sigma) as [ty|] eqn:Hlookup; [|reflexivity].
    exfalso. eapply Mem.fresh_block_alloc; [exact Halloc |]. eapply Hblocks; exact Hlookup. }
  assert (Hext : store_context_extends Sigma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)).
  { apply store_context_extends_fresh. exact Hmissing. }
  split; [exact Hext |]. split.
  - intros block ty Hlookup. destruct (Pos.eq_dec block fresh) as [Heq | Hneq].
    + subst block. eapply Mem.valid_new_block; eauto.
    + rewrite PTree.gso in Hlookup by exact Hneq.
      eapply Mem.valid_block_alloc; [exact Halloc |]. eapply Hblocks; eauto.
  - assert (Hold : aggregate_objects_valid cenv
      (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) allocated objects).
    { eapply aggregate_objects_valid_frame; [exact Hobjects | exact Hext | |].
      - intros; eapply Mem.valid_block_alloc; eauto.
      - intros; eapply Mem.perm_alloc_1; eauto. }
    destruct Hold as [Htyping Hreadable Haddress]. constructor;
      intros block base ty [Hentry | [Hb [Hbase Hty]]].
    + eapply Htyping; eauto.
    + subst block base ty. rewrite Ptrofs.unsigned_zero.
      change (object_type_at cenv (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
        fresh 0 (stored_object_type (Ptrtype (Reftype basic attr)))).
      assert (Hget : PTree.get fresh (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) =
        Some (Ptrtype (Reftype basic attr))) by apply PTree.gss.
      exact (@object_type_root cenv (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
        fresh (Ptrtype (Reftype basic attr)) Hget (proj1 Hsize)).
    + eapply Hreadable; eauto.
    + subst block base ty. eapply fresh_aggregate_readable; [exact Hkind| |exact Halloc].
      unfold Ptrofs.max_unsigned in Hsize. lia.
    + eapply Haddress; eauto.
    + subst block base ty. rewrite Ptrofs.unsigned_zero. lia.
Qed.

Print Assumptions fresh_aggregate_copy_ready.
Print Assumptions fresh_reference_aggregate_descriptors.
