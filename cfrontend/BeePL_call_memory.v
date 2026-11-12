(* Caller stored-reference validity survives callee parameter preparation. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_call_bindings BeePL_parameter_allocations.
Import ListNotations.

Lemma parameter_allocations_load_frame : forall bge Sigma vm m params vm' m' Sigma',
  alloc_variables bge Sigma vm m params vm' m' Sigma' ->
  forall b chunk ofs, Mem.valid_block m b ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros bge Sigma vm m params vm' m' Sigma' Halloc.
  induction Halloc; intros old chunk ofs Hvalid; [reflexivity |].
  unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty))
    as [allocated fresh] eqn:Hmem. inversion H; subst.
  rewrite IHHalloc.
  - eapply Mem.load_alloc_unchanged; eauto.
  - eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma parameter_allocations_valid_blocks : forall ge Sigma vm m params vm' final Sigma',
  alloc_variables ge Sigma vm m params vm' final Sigma' ->
  forall b, Mem.valid_block m b -> Mem.valid_block final b.
Proof.
  intros ge Sigma vm m params vm' final Sigma' Halloc. induction Halloc; intros b Hvalid; auto.
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [allocated fresh] eqn:Hmem.
  inversion H; subst. eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma parameter_allocations_permissions : forall ge Sigma vm m params vm' final Sigma',
  alloc_variables ge Sigma vm m params vm' final Sigma' ->
  forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm final b ofs k p.
Proof.
  intros ge Sigma vm m params vm' final Sigma' Halloc. induction Halloc; intros b ofs k p Hperm; auto.
  apply IHHalloc. unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [allocated fresh] eqn:Hmem.
  inversion H; subst. eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma parameter_preparation_load_frame :
  forall bge bookkeeping m params callee allocated bookkeeping' values final,
  alloc_variables bge bookkeeping empty_vmap m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  forall b chunk ofs, Mem.valid_block m b ->
  Mem.load chunk final b ofs = Mem.load chunk m b ofs.
Proof.
  intros bge bookkeeping m params callee allocated bookkeeping' values final
    Halloc Hnames Hbind b chunk ofs Hvalid.
  rewrite (bind_parameters_load_frame _ _ _ _ _ _ Hbind b chunk ofs).
  - eapply parameter_allocations_load_frame; eauto.
  - intros [id [ty [Hin Hlookup]]].
    destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots id ty Hin) as [target [Hget [Hfresh Hrest]]].
    assert (target = b) by congruence. subst target. contradiction.
Qed.

Lemma parameter_preparation_read_frame :
  forall bge bookkeeping m params callee allocated bookkeeping' values final,
  alloc_variables bge bookkeeping empty_vmap m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  forall b ofs ty v, deref_addr ty m b ofs Full v ->
    deref_addr ty final b ofs Full v.
Proof.
  intros bge bookkeeping m params callee allocated bookkeeping' values final
    Halloc Hnames Hbind b ofs ty v Hread.
  inversion Hread; subst.
  - match goal with Hload : Mem.loadv _ _ _ = Some _ |- _ =>
    simpl in Hload;
    assert (Hvalid : Mem.valid_block m b) by
      (apply Mem.load_valid_access in Hload; eapply Mem.valid_access_valid_block;
       eapply Mem.valid_access_implies; [exact Hload | constructor]);
    eapply deref_addr_value; eauto; simpl;
    rewrite (parameter_preparation_load_frame _ _ _ _ _ _ _ _ _ Halloc Hnames Hbind b _ _ Hvalid);
    exact Hload
  end.
  - eapply deref_addr_bytes; [reflexivity| |eassumption|eassumption|].
    + eapply bind_parameters_valid_blocks; [exact Hbind|].
      eapply parameter_allocations_valid_blocks; eauto.
    + intros position Hinside.
      apply (proj2 (bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind)).
      eapply parameter_allocations_permissions; [exact Halloc|]. eauto.
Qed.

Theorem parameter_preparation_memory_locations :
  forall bge bookkeeping m params callee allocated bookkeeping' values final
    cenv Sigma layout L,
  alloc_variables bge bookkeeping empty_vmap m params callee allocated bookkeeping' ->
  NoDup (map fst params) ->
  bind_variables bge callee allocated params values final ->
  typed_memory_layout cenv Sigma layout m ->
  memory_locations L layout m ->
  memory_locations L layout final.
Proof.
  intros bge bookkeeping m params callee allocated bookkeeping' values final
    cenv Sigma layout L Halloc Hnames Hbind Hmemory Hlocations.
  intros b ofs ty chunk Hentry v Hread.
  destruct (typed_memory_cell_read cenv empty_context Sigma m b ofs ty chunk
    (Hmemory _ _ _ _ Hentry)) as [old [Hreadold Htyped]].
  assert (v = old).
  { eapply deref_full_deterministic; [exact Hread |].
    eapply parameter_preparation_read_frame; eauto. }
  subst v. eapply Hlocations; eauto.
Qed.

Print Assumptions parameter_preparation_load_frame.
Print Assumptions parameter_preparation_memory_locations.
