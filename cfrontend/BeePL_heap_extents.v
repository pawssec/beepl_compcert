(* Extents describe source-owned data storage, not kernel packet payloads or
   compiler code blocks. In particular this is not Genv.init_mem adequacy. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_packet_state BeePL_block_extents.
Require Import BeePL_structure_proofs BeePL_call_bindings BeePL_initializer_frames.
Local Open Scope Z_scope.

Definition tracked_data_block (Sigma : store_context) (objects : aggregate_object_context)
    (cells : scalar_layout) (packets : packet_locations) (b : Values.block) : Prop :=
  (exists ty, PTree.get b Sigma = Some ty /\ is_funtype ty = false) \/
  (exists ofs ty chunk, cells b ofs ty chunk) \/
  (exists base ty, objects b base ty) \/ (exists base, packets b base).

Definition extent_context_covers Sigma objects cells packets (limits : block_extent_context) : Prop :=
  forall b, tracked_data_block Sigma objects cells packets b ->
    exists limit, PTree.get b limits = Some limit.

Definition heap_block_extents Sigma m objects cells packets : Prop :=
  exists limits, block_extents_valid m limits /\ extent_context_covers Sigma objects cells packets limits.

Lemma heap_extent_lookup : forall Sigma m objects cells packets b,
  heap_block_extents Sigma m objects cells packets ->
  tracked_data_block Sigma objects cells packets b ->
  exists limit, source_block_extent m b limit.
Proof. intros * [limits [Hvalid Hcover]] Htracked.
  destruct (Hcover _ Htracked) as [limit Hget]. exists limit. apply Hvalid; exact Hget. Qed.

Lemma heap_extents_registry_frame : forall Sigma Sigma' m objects cells packets objects' cells' packets',
  heap_block_extents Sigma m objects cells packets ->
  (forall b, tracked_data_block Sigma' objects' cells' packets' b ->
    tracked_data_block Sigma objects cells packets b) ->
  heap_block_extents Sigma' m objects' cells' packets'.
Proof. intros * [limits [Hvalid Hcover]] Horigin. exists limits; split; [exact Hvalid|].
  intros b Hin. apply Hcover, Horigin; exact Hin. Qed.

Lemma heap_extents_transport : forall Sigma m final objects cells packets,
  heap_block_extents Sigma m objects cells packets ->
  (forall b limit, source_block_extent m b limit -> source_block_extent final b limit) ->
  heap_block_extents Sigma final objects cells packets.
Proof. intros * [limits [Hvalid Hcover]] Hframe. exists limits; split; [|exact Hcover].
  intros b limit Hget. apply Hframe, Hvalid; exact Hget. Qed.

Lemma heap_extents_store : forall Sigma m final objects cells packets chunk b ofs value,
  heap_block_extents Sigma m objects cells packets ->
  Mem.store chunk m b ofs value = Some final -> heap_block_extents Sigma final objects cells packets.
Proof. intros. eapply heap_extents_transport; [eassumption|].
  intros; eapply source_block_extent_store; eauto. Qed.

Lemma heap_extents_storebytes : forall Sigma m final objects cells packets b ofs bytes,
  heap_block_extents Sigma m objects cells packets ->
  Mem.storebytes m b ofs bytes = Some final -> heap_block_extents Sigma final objects cells packets.
Proof. intros. eapply heap_extents_transport; [eassumption|].
  intros; eapply source_block_extent_storebytes; eauto. Qed.

Lemma assignment_source_extent : forall ge ty m b ofs bf v final result block limit,
  assign_addr ge ty m b ofs bf v final result -> source_block_extent m block limit ->
  source_block_extent final block limit.
Proof.
  intros * Hassign Hextent. eapply source_block_extent_transport; [exact Hextent| | |].
  - eapply assignment_preserves_valid_blocks; [exact Hassign|exact (source_extent_valid _ _ _ Hextent)].
  - intros. apply (proj2 (assignment_permissions_iff _ _ _ _ _ _ _ _ _ _ _ _ _ Hassign)); assumption.
  - intros. apply (proj1 (assignment_permissions_iff _ _ _ _ _ _ _ _ _ _ _ _ _ Hassign)); assumption.
Qed.

Lemma heap_extents_assignment : forall ge Sigma m final objects cells packets ty b ofs bf v result,
  heap_block_extents Sigma m objects cells packets -> assign_addr ge ty m b ofs bf v final result ->
  heap_block_extents Sigma final objects cells packets.
Proof. intros. eapply heap_extents_transport; [eassumption|].
  intros; eapply assignment_source_extent; eauto. Qed.

Theorem heap_extents_allocation :
  forall Sigma Sigma' m allocated objects cells packets objects' cells' packets' fresh size,
  heap_block_extents Sigma m objects cells packets ->
  Mem.alloc m 0 size = (allocated, fresh) -> 0 <= size <= Ptrofs.max_unsigned ->
  (forall b, tracked_data_block Sigma' objects' cells' packets' b ->
    tracked_data_block Sigma objects cells packets b \/ b = fresh) ->
  heap_block_extents Sigma' allocated objects' cells' packets'.
Proof.
  intros * [limits [Hvalid Hcover]] Halloc Hsize Horigin.
  exists (PTree.set fresh size limits). split; [eapply block_extents_allocation; eauto|].
  intros b Hin. destruct (peq b fresh) as [Heq|Hneq].
  - subst b. exists size. apply PTree.gss.
  - destruct (Horigin _ Hin) as [Hold|Heq]; [|contradiction].
    destruct (Hcover _ Hold) as [limit Hget]. exists limit. rewrite PTree.gso; assumption.
Qed.

Lemma tracked_data_block_same_block_extension :
  forall Sigma objects cells packets Sigma' objects' cells' packets' fresh,
  (forall b ty, PTree.get b Sigma' = Some ty -> PTree.get b Sigma = Some ty \/ b = fresh) ->
  (forall b base ty, objects' b base ty -> objects b base ty \/ b = fresh) ->
  (forall b ofs ty chunk, cells' b ofs ty chunk -> cells b ofs ty chunk \/ b = fresh) ->
  (forall b base, packets' b base -> packets b base \/ b = fresh) ->
  forall b, tracked_data_block Sigma' objects' cells' packets' b ->
    tracked_data_block Sigma objects cells packets b \/ b = fresh.
Proof.
  intros * HS HO HC HP b [[ty [Hget Hcode]]|[[ofs [ty [chunk Hcell]]]|[[base [ty Hobject]]|[base Hpacket]]]].
  - destruct (HS _ _ Hget); [left; left; eauto|auto].
  - destruct (HC _ _ _ _ Hcell); [left; right; left; eauto|auto].
  - destruct (HO _ _ _ Hobject); [left; right; right; left; eauto|auto].
  - destruct (HP _ _ Hpacket); [left; right; right; right; eauto|auto].
Qed.

Lemma heap_extents_add_object : forall Sigma m objects cells packets b base ty,
  heap_block_extents Sigma m objects cells packets ->
  tracked_data_block Sigma objects cells packets b ->
  heap_block_extents Sigma m (add_aggregate_descriptor objects b base ty) cells packets.
Proof.
  intros * Hextents Htracked. eapply heap_extents_registry_frame; [exact Hextents|].
  intros block [HS|[HC|[[offset [root [Hold|[Hb Hrest]]]]|HP]]].
  - left; exact HS.
  - right; left; exact HC.
  - right; right; left; eauto.
  - subst block; exact Htracked.
  - right; right; right; exact HP.
Qed.

Lemma array_helper_source_extent : forall ge m b base vs ty final block limit,
  sem_array_init_helper ge m b base vs ty final -> source_block_extent m block limit ->
  source_block_extent final block limit.
Proof.
  intros * Hinit. induction Hinit; intros Hextent; auto.
  apply IHHinit. eapply assignment_source_extent; eauto.
Qed.

Lemma field_initializer_source_extent : forall ge b base sid ids vs ts m final block limit,
  sem_allocate_fields ge b base sid ids vs ts m final -> source_block_extent m block limit ->
  source_block_extent final block limit.
Proof.
  intros * Hinit. induction Hinit; intros Hextent; auto.
  apply IHHinit. eapply assignment_source_extent; eauto.
Qed.

Lemma heap_extents_array_helper : forall ge Sigma m final objects cells packets b base vs ty,
  heap_block_extents Sigma m objects cells packets -> sem_array_init_helper ge m b base vs ty final ->
  heap_block_extents Sigma final objects cells packets.
Proof. intros. eapply heap_extents_transport; [eassumption|].
  intros; eapply array_helper_source_extent; eauto. Qed.

Lemma heap_extents_field_initializer : forall ge Sigma m final objects cells packets b base sid ids vs ts,
  heap_block_extents Sigma m objects cells packets -> sem_allocate_fields ge b base sid ids vs ts m final ->
  heap_block_extents Sigma final objects cells packets.
Proof. intros. eapply heap_extents_transport; [eassumption|].
  intros; eapply field_initializer_source_extent; eauto. Qed.

Lemma store_set_lookup_origin : forall (Sigma : store_context) fresh (ty : type) b (other : type),
  PTree.get b (PTree.set fresh ty Sigma) = Some other -> PTree.get b Sigma = Some other \/ b=fresh.
Proof. intros * Hget. rewrite PTree.gsspec in Hget. destruct (peq b fresh); auto. Qed.
