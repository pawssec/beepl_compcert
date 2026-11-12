(* Actual parameter preparation preserves the source-owned block profile. *)
Require Import Coqlib List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_allocation_proofs.
Require Import BeePL_scalar_parameters BeePL_call_parameters BeePL_call_parameter_layout.
Require Import BeePL_aggregate_memory BeePL_packet_state BeePL_block_extents BeePL_heap_extents.
Import ListNotations.
Local Open Scope Z_scope.

Lemma call_parameter_extent_size : forall env ty,
  call_parameter_type ty -> 0 <= sizeof_type env ty <= Ptrofs.max_unsigned.
Proof.
  intros env ty [->|Hscalar].
  - simpl. unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize;
      destruct Archi.ptr64; vm_compute; split; congruence.
  - rewrite <- (scalar_parameter_chunk_size env ty Hscalar).
    destruct (transl_bchunk_cchunk (scalar_parameter_chunk ty)); simpl;
      unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize;
      destruct Archi.ptr64; vm_compute; split; congruence.
Qed.

Lemma parameter_allocation_extents : forall ge Sigma vm m params callee allocated Sigma' objects cells packets,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  Forall (fun param => call_parameter_type (snd param)) params ->
  heap_block_extents Sigma m objects cells packets ->
  heap_block_extents Sigma' allocated objects cells packets.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' objects cells packets Ha.
  induction Ha; intros Htypes Hheap; auto.
  inversion Htypes; subst. apply IHHa; auto.
  unfold balloc in H.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [next fresh] eqn:Halloc.
  inversion H; subst.
  eapply heap_extents_allocation; [exact Hheap|exact Halloc| |].
  - apply call_parameter_extent_size; assumption.
  - eapply tracked_data_block_same_block_extension; try (intros; left; assumption).
    intros block t Hget. rewrite PTree.gsspec in Hget.
    match type of Hget with context [if ?test then _ else _] => destruct test; auto end.
Qed.

Lemma allocated_parameter_store_lookup : forall ge Sigma vm m params callee allocated Sigma',
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  NoDup (map fst params) -> store_blocks_valid Sigma m ->
  forall id ty b, In (id,ty) params -> callee ! id = Some(b,ty) -> Sigma' ! b = Some ty.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' Ha.
  induction Ha as [Sigma vm m|Sigma vm m id ty params allocated fresh final result Sigma1 Sigma' Halloc Htail IH];
    intros Hnames Hblocks name t block Hin Hget; [contradiction|].
  inversion Hnames as [|? ? Hnotin Htailnames]; subst.
  destruct (balloc_store_extension _ _ _ _ _ _ _ _ _ Hblocks Halloc) as [Hext Hblocks1].
  destruct Hin as [Heq|Hin]; [inversion Heq; subst name t|eapply IH; eauto].
  rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Htail id Hnotin) in Hget.
  rewrite PTree.gss in Hget. inversion Hget; subst block.
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Htail Hblocks1) as [HtailExt _].
  apply HtailExt. unfold balloc in Halloc.
  destruct (Mem.alloc m 0 (sizeof_type (genv_cenv ge) ty)) as [next allocatedblock].
  inversion Halloc; subst. apply PTree.gss.
Qed.

Lemma parameter_binding_extents : forall ge vm m params values final Sigma objects cells packets,
  bind_variables ge vm m params values final -> heap_block_extents Sigma m objects cells packets ->
  heap_block_extents Sigma final objects cells packets.
Proof.
  intros ge vm m params values final Sigma objects cells packets Hb.
  induction Hb; intros Hheap; auto. apply IHHb.
  eapply heap_extents_assignment; eauto.
Qed.

Theorem parameter_preparation_extents : forall ge Sigma vm m params callee allocated Sigma' values final objects cells packets,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  bind_variables ge callee allocated params values final ->
  Forall (fun param => call_parameter_type (snd param)) params ->
  NoDup (map fst params) -> store_blocks_valid Sigma m ->
  heap_block_extents Sigma m objects cells packets ->
  heap_block_extents Sigma' final objects (extended_parameter_call_layout cells callee params) packets.
Proof.
  intros * Ha Hb Htypes Hnames Hblocks Hheap.
  eapply heap_extents_registry_frame.
  - eapply parameter_binding_extents; [exact Hb|].
    eapply parameter_allocation_extents; eauto.
  - intros block [HS|[[ofs [ty [chunk [Hold|[Hscalar [id [Hin [Hget Hrest]]]]]]]]|Hrest]].
    + left; exact HS.
    + right; left; eauto.
    + left. exists ty. split.
      * eapply allocated_parameter_store_lookup; eauto.
      * destruct Hscalar as [[[pt ->]|[[bt [a ->]]|[bt [a ->]]]] Hvol]; reflexivity.
    + right; right; exact Hrest.
Qed.

Print Assumptions parameter_preparation_extents.
