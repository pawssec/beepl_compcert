(* Hereditary object/packet alias conditions, independent of heap records. *)
Require Import List ZArith Lia Integers AST Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_packet.
Require Import BeePL_packet_descriptor_copy BeePL_packet_state BeePL_packet_mutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_object_region_coherent cenv m (packets : packet_locations)
    block start root : Prop :=
  forall descriptor offset, packets descriptor offset ->
    (packet_interval_disjoint descriptor (Ptrofs.unsigned offset) packet_descriptor_size
       block start (sizeof_type cenv root) \/
     exists delta, object_path cenv root delta Bytes /\ descriptor = block /\
       Ptrofs.unsigned offset = start + delta) /\
    forall view, packet_descriptor_valid m descriptor offset view ->
      packet_interval_disjoint view.(packet_block) (Ptrofs.unsigned view.(packet_first))
        (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first))
        block start (sizeof_type cenv root).

Definition packet_object_coherence cenv m (objects : aggregate_object_context) packets : Prop :=
  forall block base root, objects block base root -> forall delta child,
    object_path cenv root delta child ->
    packet_object_region_coherent cenv m packets block (Ptrofs.unsigned base + delta) child.

Lemma packet_object_coherence_root : forall cenv m objects packets block base root,
  packet_object_coherence cenv m objects packets -> objects block base root ->
  0 <= sizeof_type cenv root ->
  packet_object_region_coherent cenv m packets block (Ptrofs.unsigned base) root.
Proof.
  intros cenv m objects packets block base root Hcoherent Hobject Hsize.
  replace (Ptrofs.unsigned base) with (Ptrofs.unsigned base + 0) by lia.
  apply Hcoherent with (root := root); [exact Hobject|constructor; exact Hsize].
Qed.

Theorem packet_object_coherence_subobject_extension : forall cenv m objects packets block base root delta child result,
  packet_object_coherence cenv m objects packets -> objects block base root ->
  object_path cenv root delta child ->
  Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  packet_object_coherence cenv m (add_aggregate_descriptor objects block result child) packets.
Proof.
  intros cenv m objects packets block base root delta child result Hcoherent Hobject Hpath Hresult
    b ofs ty [Hold|[Hb [Hofs Hty]]] offset leaf Hleaf.
  - eapply Hcoherent; eauto.
  - subst. rewrite Hresult. replace (Ptrofs.unsigned base + delta + offset)
      with (Ptrofs.unsigned base + (delta + offset)) by lia.
    eapply Hcoherent; [exact Hobject|]. eapply object_path_compose; eauto.
Qed.

Lemma packet_object_coherence_view_origins : forall cenv m final objects packets,
  packet_object_coherence cenv m objects packets ->
  (forall descriptor offset view, packets descriptor offset ->
    packet_descriptor_valid final descriptor offset view ->
    exists old old_offset, packets old old_offset /\ packet_descriptor_valid m old old_offset view) ->
  packet_object_coherence cenv final objects packets.
Proof.
  intros cenv m final objects packets Hcoherent Horigin b base root Hobject delta child Hpath descriptor offset Hin.
  split; [exact (proj1 (Hcoherent _ _ _ Hobject _ _ Hpath _ _ Hin))|].
  intros view Hview. destruct (Horigin _ _ _ Hin Hview) as [old [old_offset [Hold Hbefore]]].
  exact (proj2 (Hcoherent _ _ _ Hobject _ _ Hpath _ _ Hold) _ Hbefore).
Qed.

Theorem packet_object_coherence_scalar_store : forall cenv m final objects packets chunk block start value,
  packet_state_valid m packets -> packet_object_coherence cenv m objects packets ->
  packet_write_separated m packets block start (size_chunk chunk) ->
  Mem.store chunk m block start value = Some final ->
  packet_object_coherence cenv final objects packets.
Proof.
  intros cenv m final objects packets chunk block start value Hv Hcoherent Hsep Hstore.
  eapply packet_object_coherence_view_origins; [exact Hcoherent|].
  intros descriptor offset view Hin Hview. exists descriptor, offset. split; [exact Hin|].
  destruct (Hv _ _ Hin) as [_ [old [contents [Hbefore Hcontents]]]].
  assert (Hafter : packet_descriptor_valid final descriptor offset old).
  { eapply packet_descriptor_store_frame;
      [exact Hstore|exact (proj1 (Hsep _ _ Hin))|exact Hbefore]. }
  assert (view = old) by (eapply packet_descriptor_view_unique; eauto).
  subst; exact Hbefore.
Qed.

Theorem packet_object_coherence_allocation : forall cenv m allocated objects packets lo hi fresh,
  packet_state_valid m packets -> packet_object_coherence cenv m objects packets ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  packet_object_coherence cenv allocated objects packets.
Proof.
  intros cenv m allocated objects packets lo hi fresh Hv Hcoherent Ha.
  eapply packet_object_coherence_view_origins; [exact Hcoherent|].
  intros descriptor offset view Hin Hview. exists descriptor, offset. split; [exact Hin|].
  eapply packet_allocation_view_origin; eauto.
Qed.

