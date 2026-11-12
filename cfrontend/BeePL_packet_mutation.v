(* Replacing a Bytes descriptor changes its current packet view. Other
   descriptors and all packet payloads must survive the actual memory write.
   Separation below concerns the pre-state; it does not assume preservation. *)
Require Import List ZArith Lia Integers AST Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_packet.
Require Import BeePL_packet_descriptor_copy BeePL_packet_state BeePL_bytes_execution.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_descriptor_replacement_separated m (locations : packet_locations)
    destination target : Prop :=
  forall descriptor offset, locations descriptor offset ->
    ((descriptor = destination /\ offset = target) \/
      packet_interval_disjoint descriptor (Ptrofs.unsigned offset)
        packet_descriptor_size destination (Ptrofs.unsigned target) packet_descriptor_size) /\
    forall view, packet_descriptor_valid m descriptor offset view ->
      packet_interval_disjoint view.(packet_block) (Ptrofs.unsigned view.(packet_first))
        (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first))
        destination (Ptrofs.unsigned target) packet_descriptor_size.

Lemma bytes_assignment_memory_effect : forall ge m final source source_offset destination target result,
  assign_addr ge Bytes m destination target Full (Vloc source source_offset) final result ->
  exists bytes,
    Mem.loadbytes m source (Ptrofs.unsigned source_offset) packet_descriptor_size = Some bytes /\
    Mem.storebytes m destination (Ptrofs.unsigned target) bytes = Some final /\
    Z.of_nat (length bytes) = packet_descriptor_size /\
    Ptrofs.unsigned target + packet_descriptor_size <= Ptrofs.modulus.
Proof.
  intros ge m final source source_offset destination target result Hstep.
  inversion Hstep; subst; try discriminate.
  eexists; split; [eassumption|]. split; [eassumption|]. split; [|assumption].
  match goal with H : Mem.loadbytes _ _ _ _ = Some _ |- _ =>
    rewrite (Mem.loadbytes_length _ _ _ _ _ H), Z2Nat.id
  end; pose proof packet_descriptor_size_positive; unfold packet_descriptor_size in *; lia.
Qed.

Lemma packet_contents_descriptor_store_frame : forall m final destination target bytes view contents,
  Mem.storebytes m destination target bytes = Some final ->
  packet_view_valid m view ->
  packet_interval_disjoint view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first))
    destination target (Z.of_nat (length bytes)) ->
  Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some contents ->
  Mem.loadbytes final view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some contents.
Proof.
  intros m final destination target bytes view contents Hstore [Horder Hvalid] Hapart Hread.
  unfold packet_interval_disjoint in Hapart.
  destruct Hapart as [Hzero|Hapart].
  - rewrite Hzero in *. rewrite Mem.loadbytes_empty in * by lia; exact Hread.
  - rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore); [exact Hread|lia|exact Hapart].
Qed.

Theorem bytes_assignment_packet_state_preservation :
  forall ge m final locations source source_offset destination target result,
  packet_state_valid m locations ->
  locations source source_offset ->
  packet_descriptor_replacement_separated m locations destination target ->
  assign_addr ge Bytes m destination target Full (Vloc source source_offset) final result ->
  packet_state_valid final (extend_packet_locations locations destination target).
Proof.
  intros ge m final locations source source_offset destination target result
    Hstate Hsource Hseparate Hstep.
  destruct (bytes_assignment_memory_effect _ _ _ _ _ _ _ _ Hstep)
    as [bytes [Hread [Hstore [Hlength Hbound]]]].
  destruct (Hstate _ _ Hsource) as [HsourceBound [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
  destruct (bytes_assignment_descriptor_preservation _ _ _ _ _ _ _ _ _ Hdescriptor Hstep)
    as [Hresult HnewDescriptor].
  assert (HnewState : Ptrofs.unsigned target + packet_descriptor_size <= Ptrofs.modulus /\
    exists view contents, packet_descriptor_valid final destination target view /\
      Mem.loadbytes final view.(packet_block) (Ptrofs.unsigned view.(packet_first))
        (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some contents /\
      initialized_packet_contents contents).
  { split; [exact Hbound|]. exists view, contents. split; [exact HnewDescriptor|].
    split; [|exact Hinitialized].
    eapply packet_contents_descriptor_store_frame; [exact Hstore|exact (proj2 (proj2 Hdescriptor))| |exact Hcontents].
    rewrite Hlength. exact (proj2 (Hseparate _ _ Hsource) _ Hdescriptor). }
  intros descriptor offset [Hold|[Heqb Heqo]]; [|subst; exact HnewState].
  destruct (Hseparate _ _ Hold) as [[Hequal|Hapart] Hpayload].
  - destruct Hequal; subst; exact HnewState.
  - destruct (Hstate _ _ Hold) as [HoldBound [oldview [oldcontents [HoldDescriptor [HoldContents HoldInitialized]]]]].
    split; [exact HoldBound|]. exists oldview, oldcontents. split.
    + eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |exact HoldDescriptor].
      rewrite Hlength. unfold packet_interval_disjoint in Hapart.
      pose proof packet_descriptor_size_positive. intuition lia.
    + split; [|exact HoldInitialized].
      eapply packet_contents_descriptor_store_frame; [exact Hstore|exact (proj2 (proj2 HoldDescriptor))| |exact HoldContents].
      rewrite Hlength. exact (Hpayload _ HoldDescriptor).
Qed.

Print Assumptions bytes_assignment_packet_state_preservation.

Lemma packet_descriptor_view_unique : forall m descriptor offset first second,
  packet_descriptor_valid m descriptor offset first ->
  packet_descriptor_valid m descriptor offset second -> first = second.
Proof.
  intros m descriptor offset [b1 start1 end1] [b2 start2 end2]
    [Hfirst [Hlast Hview]] [Hfirst' [Hlast' Hview']]. simpl in *.
  assert (Values.Vptr b1 start1 = Values.Vptr b2 start2) by congruence.
  assert (Values.Vptr b1 end1 = Values.Vptr b2 end2) by congruence.
  congruence.
Qed.

(* A copied descriptor can only expose a view already tracked before the
   write. This is what lets scalar/packet separation survive replacement. *)
Theorem bytes_assignment_packet_view_origin :
  forall ge m final locations source source_offset destination target result,
  packet_state_valid m locations ->
  locations source source_offset ->
  packet_descriptor_replacement_separated m locations destination target ->
  assign_addr ge Bytes m destination target Full (Vloc source source_offset) final result ->
  forall descriptor offset view,
    extend_packet_locations locations destination target descriptor offset ->
    packet_descriptor_valid final descriptor offset view ->
    exists old old_offset, locations old old_offset /\
      packet_descriptor_valid m old old_offset view.
Proof.
  intros ge m final locations source source_offset destination target result
    Hstate Hsource Hseparate Hstep.
  destruct (bytes_assignment_memory_effect _ _ _ _ _ _ _ _ Hstep)
    as [bytes [Hread [Hstore [Hlength Hbound]]]].
  destruct (Hstate _ _ Hsource) as [HsourceBound [sourceview [contents [HsourceDescriptor Hcontents]]]].
  destruct (bytes_assignment_descriptor_preservation _ _ _ _ _ _ _ _ _ HsourceDescriptor Hstep)
    as [Hresult HnewDescriptor].
  assert (HnewOrigin : forall view,
    packet_descriptor_valid final destination target view ->
    exists old old_offset, locations old old_offset /\
      packet_descriptor_valid m old old_offset view).
  { intros view Hview.
    assert (view = sourceview) by (eapply packet_descriptor_view_unique; eauto).
    subst view. exists source, source_offset; auto. }
  intros descriptor offset view [Hold|[Heqb Heqo]] Hview; [|subst; auto].
  destruct (Hseparate _ _ Hold) as [[Hequal|Hapart] Hpayload].
  - destruct Hequal; subst; auto.
  - destruct (Hstate _ _ Hold) as [HoldBound [oldview [oldcontents [HoldDescriptor HoldContents]]]].
    assert (HoldFinal : packet_descriptor_valid final descriptor offset oldview).
    { eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |exact HoldDescriptor].
      rewrite Hlength. unfold packet_interval_disjoint in Hapart.
      pose proof packet_descriptor_size_positive. intuition lia. }
    assert (view = oldview) by (eapply packet_descriptor_view_unique; eauto).
    subst view. exists descriptor, offset; auto.
Qed.

Theorem bytes_assignment_preserves_write_separation :
  forall ge m final locations source source_offset destination target result written start count,
  packet_state_valid m locations ->
  locations source source_offset ->
  packet_descriptor_replacement_separated m locations destination target ->
  assign_addr ge Bytes m destination target Full (Vloc source source_offset) final result ->
  packet_write_separated m locations written start count ->
  packet_write_separated final locations written start count.
Proof.
  intros ge m final locations source source_offset destination target result written start count
    Hstate Hsource Hreplace Hstep Hseparate descriptor offset Hentry.
  split; [exact (proj1 (Hseparate _ _ Hentry))|].
  intros view Hview.
  destruct (bytes_assignment_packet_view_origin _ _ _ _ _ _ _ _ _
    Hstate Hsource Hreplace Hstep descriptor offset view (or_introl Hentry) Hview)
    as [old [old_offset [Hold HoldView]]].
  exact (proj2 (Hseparate _ _ Hold) _ HoldView).
Qed.

Print Assumptions bytes_assignment_packet_view_origin.
Print Assumptions bytes_assignment_preserves_write_separation.

Theorem packet_state_allocation_preserved : forall m locations lo hi allocated fresh,
  packet_state_valid m locations ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  packet_state_valid allocated locations.
Proof.
  intros m locations lo hi allocated fresh Hstate Halloc descriptor offset Hentry.
  destruct (Hstate _ _ Hentry) as [Hbound [view [contents [Hdescriptor [Hread Hinitialized]]]]].
  split; [exact Hbound|]. exists view, contents. split.
  - eapply packet_descriptor_alloc_frame; eauto.
  - split; [|exact Hinitialized].
    rewrite (Mem.loadbytes_alloc_unchanged _ _ _ _ _ Halloc); [exact Hread|].
    exact (proj1 (proj2 (proj2 (proj2 Hdescriptor)))).
Qed.

Lemma packet_allocation_view_origin : forall m locations lo hi allocated fresh descriptor offset view,
  packet_state_valid m locations ->
  Mem.alloc m lo hi = (allocated, fresh) -> locations descriptor offset ->
  packet_descriptor_valid allocated descriptor offset view ->
  packet_descriptor_valid m descriptor offset view.
Proof.
  intros m locations lo hi allocated fresh descriptor offset view Hstate Halloc Hentry Hview.
  destruct (Hstate _ _ Hentry) as [Hbound [oldview [contents [Hold Hcontents]]]].
  assert (Hallocated : packet_descriptor_valid allocated descriptor offset oldview)
    by (eapply packet_descriptor_alloc_frame; eauto).
  assert (view = oldview) by (eapply packet_descriptor_view_unique; eauto).
  subst view; exact Hold.
Qed.

Theorem packet_allocation_preserves_write_separation :
  forall m locations lo hi allocated fresh written start count,
  packet_state_valid m locations ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  packet_write_separated m locations written start count ->
  packet_write_separated allocated locations written start count.
Proof.
  intros m locations lo hi allocated fresh written start count Hstate Halloc Hseparate
    descriptor offset Hentry.
  split; [exact (proj1 (Hseparate _ _ Hentry))|].
  intros view Hview. apply (proj2 (Hseparate _ _ Hentry) view).
  eapply packet_allocation_view_origin; eauto.
Qed.

Theorem packet_allocation_fresh_write_separated :
  forall m locations lo hi allocated fresh start count,
  packet_state_valid m locations ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  packet_write_separated allocated locations fresh start count.
Proof.
  intros m locations lo hi allocated fresh start count Hstate Halloc descriptor offset Hentry.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hfresh.
  destruct (Hstate _ _ Hentry) as [Hbound [view [contents [Hdescriptor Hcontents]]]].
  split.
  - right; left. intro Heq; subst descriptor. apply Hfresh.
    eapply packet_descriptor_source_block; eauto.
  - intros current Hcurrent. right; left. intro Heq. apply Hfresh.
    pose proof (packet_allocation_view_origin _ _ _ _ _ _ _ _ _ Hstate Halloc Hentry Hcurrent) as Hold.
    rewrite <- Heq. exact (proj1 (proj2 (proj2 (proj2 Hold)))).
Qed.

Print Assumptions packet_state_allocation_preserved.
Print Assumptions packet_allocation_preserves_write_separation.
Print Assumptions packet_allocation_fresh_write_separated.
