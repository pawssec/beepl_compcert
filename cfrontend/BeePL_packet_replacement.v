(* In-place aggregate copies may replace complete registered descriptors.
   The plan describes only source-state locations and write footprints. *)
Require Import List ZArith Lia Integers AST Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_packet.
Require Import BeePL_packet_descriptor_copy BeePL_packet_state BeePL_packet_mutation BeePL_packet_heap.
Require Import BeePL_copy_bytes BeePL_packet_object_layout.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_copy_replacement_plan m (packets : packet_locations)
    source source_start destination target count : Prop :=
  (forall descriptor offset, packets descriptor offset ->
    packet_interval_disjoint descriptor (Ptrofs.unsigned offset) packet_descriptor_size destination target count \/
    exists delta source_offset,
      descriptor = destination /\ Ptrofs.unsigned offset = target + delta /\
      packets source source_offset /\ Ptrofs.unsigned source_offset = source_start + delta /\
      0 <= delta /\ delta + packet_descriptor_size <= count /\
      (align_chunk Mptr | target + delta)) /\
  (forall descriptor offset, packets descriptor offset -> forall view,
    packet_descriptor_valid m descriptor offset view ->
    packet_interval_disjoint view.(packet_block) (Ptrofs.unsigned view.(packet_first))
      (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) destination target count).

Lemma copied_packet_descriptor_at_offset :
  forall m final source source_start destination target count bytes delta source_offset target_offset view,
  Mem.loadbytes m source source_start count = Some bytes ->
  Mem.storebytes m destination target bytes = Some final ->
  0 <= delta -> delta + packet_descriptor_size <= count ->
  Ptrofs.unsigned source_offset = source_start + delta ->
  Ptrofs.unsigned target_offset = target + delta ->
  (align_chunk Mptr | target + delta) ->
  packet_descriptor_valid m source source_offset view ->
  packet_descriptor_valid final destination target_offset view.
Proof.
  intros m final source source_start destination target count bytes delta source_offset target_offset view
    Hread Hstore Hdelta Hbound Hsource Htarget Halign [Hfirst [Hlast Hview]].
  unfold packet_descriptor_valid. rewrite Htarget. rewrite Hsource in Hfirst, Hlast.
  pose proof (size_chunk_pos Mptr) as Hpositive. unfold packet_descriptor_size in Hbound.
  split.
  - eapply copied_bytes_scalar_load; eauto; lia.
  - split.
    + replace (target + delta + size_chunk Mptr) with (target + (delta + size_chunk Mptr)) by lia.
      eapply copied_bytes_scalar_load with (delta := delta + size_chunk Mptr) (total := count); eauto; try lia.
      * replace (target + (delta + size_chunk Mptr)) with (target + delta + size_chunk Mptr) by lia.
        apply Z.divide_add_r; [exact Halign|apply pointer_slot_alignment].
      * replace (source_start + (delta + size_chunk Mptr)) with (source_start + delta + size_chunk Mptr) by lia.
        exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Theorem packet_copy_replacement_state :
  forall m final packets source source_start destination target count bytes,
  0 <= count -> packet_state_valid m packets ->
  packet_copy_replacement_plan m packets source source_start destination target count ->
  Mem.loadbytes m source source_start count = Some bytes ->
  Mem.storebytes m destination target bytes = Some final ->
  packet_state_valid final packets /\
  (forall descriptor offset view, packets descriptor offset ->
    packet_descriptor_valid final descriptor offset view ->
    exists old old_offset, packets old old_offset /\ packet_descriptor_valid m old old_offset view).
Proof.
  intros m final packets source source_start destination target count bytes Hcount Hv [Hslots Hpayload] Hread Hstore.
  assert (Hlength : Z.of_nat (length bytes) = count).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hread), Z2Nat.id by exact Hcount. reflexivity. }
  assert (Htransport : forall descriptor offset, packets descriptor offset ->
    exists old old_offset view contents,
      packets old old_offset /\ packet_descriptor_valid m old old_offset view /\
      packet_descriptor_valid final descriptor offset view /\
      Mem.loadbytes final view.(packet_block) (Ptrofs.unsigned view.(packet_first))
        (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some contents /\
      initialized_packet_contents contents).
  { intros descriptor offset Hin.
    destruct (Hslots _ _ Hin) as [Hapart|[delta [source_offset [Hd [Ho [Hs [Hso [Hdelta [Hbound Halign]]]]]]]]].
    - destruct (Hv _ _ Hin) as [_ [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
      exists descriptor, offset, view, contents. split; [exact Hin|]. split; [exact Hdescriptor|]. split.
      + eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |exact Hdescriptor].
        rewrite Hlength. unfold packet_interval_disjoint in Hapart.
        pose proof packet_descriptor_size_positive; intuition lia.
      + split; [|exact Hinitialized]. eapply packet_contents_descriptor_store_frame;
          [exact Hstore|exact (proj2 (proj2 Hdescriptor))| |exact Hcontents].
        rewrite Hlength. eapply Hpayload; eauto.
    - subst descriptor. destruct (Hv _ _ Hs) as [_ [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
      exists source, source_offset, view, contents. split; [exact Hs|]. split; [exact Hdescriptor|]. split.
      + eapply copied_packet_descriptor_at_offset with (bytes := bytes) (count := count) (delta := delta) (source := source) (source_start := source_start) (target := target) (source_offset := source_offset); eauto.
      + split; [|exact Hinitialized]. eapply packet_contents_descriptor_store_frame;
          [exact Hstore|exact (proj2 (proj2 Hdescriptor))| |exact Hcontents].
        rewrite Hlength. eapply Hpayload; eauto. }
  split.
  - intros descriptor offset Hin. split; [exact (proj1 (Hv _ _ Hin))|].
    destruct (Htransport _ _ Hin) as [old [old_offset [view [contents [Hold [Hbefore [Hafter [Hcontents Hinitialized]]]]]]]].
    exists view, contents; auto.
  - intros descriptor offset view Hin Hview.
    destruct (Htransport _ _ Hin) as [old [old_offset [actual [contents [Hold [Hbefore [Hafter Hrest]]]]]]].
    assert (view = actual) by (eapply packet_descriptor_view_unique; eauto).
    subst. exists old, old_offset; auto.
Qed.

Theorem packet_heap_copy_replacement :
  forall ge Sigma m final objects cells packets source source_start destination target count bytes,
  0 <= count -> packet_heap_invariant ge Sigma m objects cells packets ->
  packet_copy_replacement_plan m packets source source_start destination target count ->
  Mem.loadbytes m source source_start count = Some bytes ->
  Mem.storebytes m destination target bytes = Some final ->
  packet_heap_invariant ge Sigma final objects cells packets.
Proof.
  intros ge Sigma m final objects cells packets source source_start destination target count bytes
    Hcount [Hv Ht Hc Hsep Hcoherent] Hplan Hread Hstore.
  destruct (packet_copy_replacement_state _ _ _ _ _ _ _ _ _ Hcount Hv Hplan Hread Hstore) as [Hv' Horigin].
  constructor; auto.
  - intros b ofs ty chunk Hcell descriptor offset Hin.
    split; [exact (proj1 (Hsep _ _ _ _ Hcell _ _ Hin))|].
    intros view Hview. destruct (Horigin _ _ _ Hin Hview) as [old [old_offset [Hold Hbefore]]].
    exact (proj2 (Hsep _ _ _ _ Hcell _ _ Hold) _ Hbefore).
  - eapply packet_object_coherence_view_origins; eauto.
Qed.
Print Assumptions packet_heap_copy_replacement.
