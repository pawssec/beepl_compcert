(* Initializers change contents, but retain existing permissions and aggregate
   descriptors. This does not assert that the new contents are well typed. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_structure_proofs.
Require Import BeePL_array_proofs BeePL_aggregate_memory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma assignment_preserves_permissions : forall ge ty m dst offset bf v m' result,
  assign_addr ge ty m dst offset bf v m' result ->
  forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.
Proof.
  intros ge ty m dst offset bf v m' result Hassign b ofs k p Hperm.
  inversion Hassign; subst;
    try solve [match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.perm_store_1; eauto end].
  - eapply Mem.perm_storebytes_1; eauto.
  - match goal with H : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.perm_store_1; eauto end.
  - eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma array_helper_preserves_permissions : forall ge m b base vs ty m',
  sem_array_init_helper ge m b base vs ty m' ->
  forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p.
Proof.
  intros ge m b base vs ty m' Hinit. induction Hinit; intros; auto.
  apply IHHinit. eapply assignment_preserves_permissions; eauto.
Qed.

Lemma field_initializer_preserves_permissions : forall ge b base sid ids vs ts m m',
  sem_allocate_fields ge b base sid ids vs ts m m' ->
  forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p.
Proof.
  intros ge b base sid ids vs ts m m' Hinit. induction Hinit; intros; auto.
  apply IHHinit. eapply assignment_preserves_permissions; eauto.
Qed.

Lemma variable_allocation_preserves_permissions : forall ge Sigma vm m vars vm' m' Sigma',
  alloc_variables ge Sigma vm m vars vm' m' Sigma' ->
  forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p.
Proof.
  intros ge Sigma vm m vars vm' m' Sigma' Halloc. induction Halloc; intros; auto.
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type ge.(genv_cenv) ty)) as [allocated fresh] eqn:Hmem.
  inversion H; subst. eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma actual_array_initialization_shape :
  forall ge Sigma arr ty vs vm m vm' m' Sigma',
  sem_array_init ge Sigma arr ty vs vm m vm' m' Sigma' ->
  exists elem len attr allocated fresh,
    ty = Atype elem len attr /\ len = Z.of_nat (length vs) /\
    Mem.alloc m 0 (sizeof_type ge.(genv_cenv) ty) = (allocated, fresh) /\
    vm' = PTree.set arr (fresh, ty) vm /\ Sigma' = PTree.set fresh ty Sigma /\
    sem_array_init_helper ge allocated fresh Ptrofs.zero vs elem m'.
Proof.
  intros ge Sigma arr ty vs vm m vm' m' Sigma' Hinit. inversion Hinit; subst.
  match goal with Halloc : alloc_variables _ _ _ _ [(arr, _)] _ _ _ |- _ =>
    destruct (singleton_allocation_maps _ _ _ _ _ _ _ _ _ Halloc)
      as [fresh [Hvm [HS Hmem]]]
  end.
  assert (loc = fresh).
  { match goal with Hlookup : PTree.get arr vm' = Some _ |- _ =>
      rewrite Hvm, PTree.gss in Hlookup; inversion Hlookup; reflexivity end. }
  subst loc. do 5 eexists. repeat split; eauto.
Qed.

Theorem array_initialization_preserves_descriptors :
  forall ge cenv Sigma Sigma' objects arr ty vs vm m vm' m',
  sem_array_init ge Sigma arr ty vs vm m vm' m' Sigma' ->
  aggregate_objects_valid cenv Sigma m objects -> store_context_extends Sigma Sigma' ->
  aggregate_objects_valid cenv Sigma' m' objects.
Proof.
  intros ge cenv Sigma Sigma' objects arr ty vs vm m vm' m' Hinit Hobjects Hext.
  destruct (actual_array_initialization_shape _ _ _ _ _ _ _ _ _ _ Hinit)
    as [elem [len [attr [allocated [fresh [Hty [Hlen [Halloc [Hvm [HS Hhelper]]]]]]]]]].
  eapply aggregate_objects_valid_frame; [exact Hobjects |exact Hext | |].
  - intros b Hvalid. eapply array_initialization_preserves_valid_blocks; [exact Hhelper|].
    eapply Mem.valid_block_alloc; eauto.
  - intros b ofs k p Hperm. eapply array_helper_preserves_permissions; [exact Hhelper|].
    eapply Mem.perm_alloc_1; eauto.
Qed.

Theorem allocated_array_helper_full_range : forall ge m allocated fresh size vs elem final,
  Mem.alloc m 0 size = (allocated, fresh) ->
  sem_array_init_helper ge allocated fresh Ptrofs.zero vs elem final ->
  Mem.valid_block final fresh /\ Mem.range_perm final fresh 0 size Cur Freeable.
Proof.
  intros ge m allocated fresh size vs elem final Halloc Hhelper. split.
  - eapply array_initialization_preserves_valid_blocks; [exact Hhelper|].
    eapply Mem.valid_new_block; eauto.
  - intros ofs Hwithin. eapply array_helper_preserves_permissions; [exact Hhelper|].
    eapply Mem.perm_alloc_2; eauto.
Qed.

Print Assumptions assignment_preserves_permissions.
Print Assumptions variable_allocation_preserves_permissions.
Print Assumptions actual_array_initialization_shape.
Print Assumptions array_initialization_preserves_descriptors.
Print Assumptions allocated_array_helper_full_range.

Lemma sem_array_elements_permissions : forall ge m b base vs ty m',
  sem_array_init_helper ge m b base vs ty m' ->
  forall block ofs k p, Mem.perm m block ofs k p -> Mem.perm m' block ofs k p.
Proof. exact array_helper_preserves_permissions. Qed.

Lemma array_initialization_allocation_shape :
  forall ge Sigma arr elem len attr vs vm m vm' final Sigma',
  sem_array_init ge Sigma arr (Atype elem len attr) vs vm m vm' final Sigma' ->
  exists allocated fresh,
    Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Atype elem len attr)) = (allocated, fresh) /\
    PTree.get arr vm' = Some (fresh, Atype elem len attr) /\
    sem_array_init_helper ge allocated fresh Ptrofs.zero vs elem final /\
    len = Z.of_nat (length vs) /\ Sigma' = PTree.set fresh (Atype elem len attr) Sigma /\
    vm' = PTree.set arr (fresh, Atype elem len attr) vm.
Proof.
  intros ge Sigma arr elem len attr vs vm m vm' final Sigma' Hinit.
  destruct (actual_array_initialization_shape _ _ _ _ _ _ _ _ _ _ Hinit)
    as [elem' [len' [attr' [allocated [fresh [Hty [Hlen [Halloc [Hvm [HS Hhelper]]]]]]]]]].
  inversion Hty; subst. exists allocated, fresh.
  split; [exact Halloc|]. split; [apply PTree.gss|].
  repeat split; auto.
Qed.

Print Assumptions array_initialization_allocation_shape.
