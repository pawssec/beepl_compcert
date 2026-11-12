(* Embedded Bytes descriptors are copied with their enclosing source object.
   Packet payloads remain in their original blocks. The destination registry
   follows declared object paths, not every overlapping source-memory view. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_aggregate_memory.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_copy_bytes BeePL_fresh_copy.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy.
Require Import BeePL_packet_object_layout.
Require Import BeePL_packet_coverage BeePL_packet_mutation BeePL_packet_heap.
Import ListNotations.
Local Open Scope Z_scope.

Definition copied_object_packets cenv (packets : packet_locations) root fresh : packet_locations :=
  fun b ofs => packets b ofs \/
    (b = fresh /\ exists delta, object_path cenv root delta Bytes /\ ofs = Ptrofs.repr delta).

Definition packet_object_copy_alignment cenv root : Prop :=
  forall delta, object_path cenv root delta Bytes -> (align_chunk Mptr | delta).

Lemma copied_object_packets_extends : forall cenv packets root fresh b ofs,
  packets b ofs -> copied_object_packets cenv packets root fresh b ofs.
Proof. intros; left; assumption. Qed.

Lemma bytes_path_relative_bound : forall cenv root delta,
  sizeof_type cenv root <= Ptrofs.modulus -> object_path cenv root delta Bytes ->
  0 <= delta <= Ptrofs.max_unsigned /\ delta + packet_descriptor_size <= sizeof_type cenv root.
Proof.
  intros cenv root delta Hbound Hpath.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hsize Hinside]].
  change (delta + packet_descriptor_size <= sizeof_type cenv root) in Hinside.
  pose proof packet_descriptor_size_positive. unfold Ptrofs.max_unsigned; lia.
Qed.

Theorem copied_embedded_packet_descriptor :
  forall cenv root m final source start fresh bytes delta view,
  sizeof_type cenv root <= Ptrofs.modulus ->
  object_path cenv root delta Bytes -> (align_chunk Mptr | delta) ->
  Ptrofs.unsigned (Ptrofs.repr (start + delta)) = start + delta ->
  packet_descriptor_valid m source (Ptrofs.repr (start + delta)) view ->
  Mem.loadbytes m source start (sizeof_type cenv root) = Some bytes ->
  Mem.storebytes m fresh 0 bytes = Some final ->
  packet_descriptor_valid final fresh (Ptrofs.repr delta) view.
Proof.
  intros cenv root m final source start fresh bytes delta view Hbound Hpath Halign
    Hoffset [Hfirst [Hlast Hview]] Hread Hstore.
  destruct (bytes_path_relative_bound _ _ _ Hbound Hpath) as [Hdelta Hinside].
  rewrite Hoffset in Hfirst, Hlast.
  unfold packet_descriptor_valid. rewrite Ptrofs.unsigned_repr by exact Hdelta.
  pose proof (size_chunk_pos Mptr) as Hpointer.
  split.
  - replace delta with (0 + delta) by lia.
    eapply copied_bytes_scalar_load; eauto; unfold packet_descriptor_size in Hinside; lia.
  - split.
    + replace (delta + size_chunk Mptr) with (0 + (delta + size_chunk Mptr)) by lia.
      eapply copied_bytes_scalar_load with (delta := delta + size_chunk Mptr)
        (total := sizeof_type cenv root); eauto; try (unfold packet_descriptor_size in Hinside; lia).
      * change (align_chunk Mptr | delta + size_chunk Mptr).
        apply Z.divide_add_r; [exact Halign|apply pointer_slot_alignment].
      * replace (start + (delta + size_chunk Mptr)) with (start + delta + size_chunk Mptr) by lia.
        exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma fresh_object_copy_old_bytes : forall m allocated final fresh lo hi bytes,
  Mem.alloc m lo hi = (allocated, fresh) -> Mem.storebytes allocated fresh 0 bytes = Some final ->
  forall old start count, Mem.valid_block m old -> 0 <= count ->
  Mem.loadbytes final old start count = Mem.loadbytes m old start count.
Proof.
  intros m allocated final fresh lo hi bytes Halloc Hstore old start count Hold Hcount.
  assert (Hapart : old <> fresh) by (intro Heq; subst; eapply Mem.fresh_block_alloc; eauto).
  rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore) by (auto; lia).
  eapply Mem.loadbytes_alloc_unchanged; eauto.
Qed.

Theorem fresh_object_copy_packet_state :
  forall ge Sigma m allocated final objects packets source base root fresh bytes,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects source base root ->
  packet_object_coverage ge.(genv_cenv) objects packets -> packet_state_valid m packets ->
  packet_object_copy_alignment ge.(genv_cenv) root ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) root) = (allocated, fresh) ->
  Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  packet_state_valid final (copied_object_packets ge.(genv_cenv) packets root fresh).
Proof.
  intros ge Sigma m allocated final objects packets source base root fresh bytes
    Hobjects Hsource Hcoverage Hpackets Halign Halloc Hread Hstore.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
    as [Hkind [Hsize [Hextent Hrest]]].
  assert (Htotal : sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus)
    by (pose proof (Ptrofs.unsigned_range base); lia).
  assert (Hold : packet_state_valid final packets).
  { eapply packet_state_storebytes_preserved; [| |exact Hstore].
    - eapply packet_state_allocation_preserved; eauto.
    - eapply packet_allocation_fresh_write_separated; eauto. }
  intros descriptor offset [Hentry|[Heqb [delta [Hpath Heqo]]]].
  - exact (Hold _ _ Hentry).
  - subst descriptor offset.
    destruct (bytes_path_relative_bound _ _ _ Htotal Hpath) as [Hdelta Hinside].
    pose proof (Hcoverage _ _ _ Hsource _ Hpath) as Hentry.
    destruct (Hpackets _ _ Hentry) as [HsourceBound [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
    destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hsource Hpath)
      as [_ [Hoffset Hbound]].
    split; [rewrite Ptrofs.unsigned_repr by exact Hdelta; lia|].
    exists view, contents. split.
    + eapply copied_embedded_packet_descriptor with (m := allocated) (bytes := bytes); eauto.
      eapply packet_descriptor_alloc_frame; eauto.
    + split; [|exact Hinitialized].
      rewrite (fresh_object_copy_old_bytes _ _ _ _ _ _ _ Halloc Hstore).
      * exact Hcontents.
      * exact (proj1 (proj2 (proj2 (proj2 Hdescriptor)))).
      * pose proof (proj1 (proj2 (proj2 Hdescriptor))); lia.
Qed.

Theorem copied_object_packets_typed : forall cenv Sigma larger packets root fresh,
  store_context_extends Sigma larger -> packet_state_typed cenv Sigma packets ->
  sizeof_type cenv root <= Ptrofs.modulus ->
  object_type_at cenv larger fresh 0 root ->
  packet_state_typed cenv larger (copied_object_packets cenv packets root fresh).
Proof.
  intros cenv Sigma larger packets root fresh Hext Htyped Hbound Hroot b ofs [Hold|[Hb [delta [Hpath Hofs]]]].
  - eapply object_type_at_store_extension; eauto.
  - subst b ofs. destruct (bytes_path_relative_bound _ _ _ Hbound Hpath) as [Hdelta _].
    rewrite Ptrofs.unsigned_repr by exact Hdelta.
    replace delta with (0 + delta) by lia. eapply object_path_typing; eauto.
Qed.

Theorem copied_object_packets_coverage : forall cenv objects packets root fresh,
  packet_object_coverage cenv objects packets ->
  packet_object_coverage cenv (add_aggregate_descriptor objects fresh Ptrofs.zero root)
    (copied_object_packets cenv packets root fresh).
Proof.
  intros cenv objects packets root fresh Hcoverage b base ty [Hold|[Hb [Hbase Hty]]] delta Hpath.
  - left; eapply Hcoverage; eauto.
  - subst b base ty. right; split; [reflexivity|]. exists delta; split; [exact Hpath|].
    rewrite Ptrofs.unsigned_zero; reflexivity.
Qed.

Print Assumptions fresh_object_copy_packet_state.
Print Assumptions copied_object_packets_typed.
Print Assumptions copied_object_packets_coverage.

Lemma fresh_object_copy_old_descriptor : forall m allocated final fresh lo hi bytes b ofs view,
  Mem.alloc m lo hi = (allocated, fresh) -> Mem.storebytes allocated fresh 0 bytes = Some final ->
  packet_descriptor_valid m b ofs view -> packet_descriptor_valid final b ofs view.
Proof.
  intros m allocated final fresh lo hi bytes b ofs view Halloc Hstore Hdescriptor.
  eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |].
  - left. intro Heq; subst b. eapply Mem.fresh_block_alloc; [exact Halloc|].
    eapply packet_descriptor_source_block; eauto.
  - eapply packet_descriptor_alloc_frame; eauto.
Qed.

Theorem fresh_object_copy_packet_view_origin :
  forall ge Sigma m allocated final objects packets source base root fresh bytes,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects source base root ->
  packet_object_coverage ge.(genv_cenv) objects packets -> packet_state_valid m packets ->
  packet_object_copy_alignment ge.(genv_cenv) root ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) root) = (allocated, fresh) ->
  Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  forall b ofs view, copied_object_packets ge.(genv_cenv) packets root fresh b ofs ->
  packet_descriptor_valid final b ofs view ->
  exists old old_offset, packets old old_offset /\ packet_descriptor_valid m old old_offset view.
Proof.
  intros ge Sigma m allocated final objects packets source base root fresh bytes
    Hobjects Hsource Hcoverage Hpackets Halign Halloc Hread Hstore b ofs view Hentry Hview.
  destruct Hentry as [Hold|[Hb [delta [Hpath Hofs]]]].
  - destruct (Hpackets _ _ Hold) as [_ [oldview [contents [Hdescriptor Hcontents]]]].
    assert (Hsame : packet_descriptor_valid final b ofs oldview)
      by (eapply fresh_object_copy_old_descriptor; eauto).
    assert (view = oldview) by (eapply packet_descriptor_view_unique; eauto).
    subst view; eauto.
  - subst b ofs. pose proof (Hcoverage _ _ _ Hsource _ Hpath) as Hold.
    destruct (Hpackets _ _ Hold) as [_ [oldview [contents [Hdescriptor Hcontents]]]].
    destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hsource Hpath)
      as [_ [Hoffset Hbound]].
    pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
      as [_ [_ [Hextent Hrest]]].
    assert (Htotal : sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus)
      by (pose proof (Ptrofs.unsigned_range base); lia).
    assert (Hsame : packet_descriptor_valid final fresh (Ptrofs.repr delta) oldview).
    { eapply copied_embedded_packet_descriptor with (m := allocated) (bytes := bytes); eauto.
      eapply packet_descriptor_alloc_frame; eauto. }
    assert (view = oldview) by (eapply packet_descriptor_view_unique; eauto).
    subst view; eauto.
Qed.

Theorem fresh_object_copy_packet_separation :
  forall ge Sigma m allocated final objects packets cells source base root fresh bytes,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects source base root ->
  packet_object_coverage ge.(genv_cenv) objects packets -> packet_state_valid m packets ->
  packet_object_copy_alignment ge.(genv_cenv) root ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> packet_layout_separated m packets cells ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) root) = (allocated, fresh) ->
  Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  packet_layout_separated final (copied_object_packets ge.(genv_cenv) packets root fresh)
    (fresh_copy_layout cells source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) fresh).
Proof.
  intros ge Sigma m allocated final objects packets cells source base root fresh bytes
    Hobjects Hsource Hcoverage Hpackets Halign Hcells Hseparate Halloc Hread Hstore.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hfresh.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
    as [_ [_ [Hextent Hrest]]].
  assert (Htotal : sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus)
    by (pose proof (Ptrofs.unsigned_range base); lia).
  assert (HcellBlock : forall b ofs ty chunk, cells b ofs ty chunk -> Mem.valid_block m b).
  { intros cellblock celloffset celltype cellchunk Hentry.
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure.
    exact (Hcells cellblock celloffset celltype cellchunk Hentry). }
  intros b ofs ty chunk Hcell descriptor offset Hpacket. split.
  - destruct Hcell as [HoldCell|[Hb [oldofs [cellDelta [HsourceCell [HsourceOfs [Hdelta [Hlimit Hofs]]]]]]]];
      destruct Hpacket as [HoldPacket|[Hdescriptor [delta [Hpath Hoffset]]]].
    + exact (proj1 (Hseparate _ _ _ _ HoldCell _ _ HoldPacket)).
    + subst descriptor offset. right; left. intro Heq; subst b. apply Hfresh; eapply HcellBlock; eauto.
    + subst b ofs. right; left. intro Heq; subst descriptor. apply Hfresh.
      destruct (Hpackets _ _ HoldPacket) as [_ [view [contents [Hvalid Hcontents]]]].
      eapply packet_descriptor_source_block; eauto.
    + subst b ofs descriptor offset.
      pose proof (Hcoverage _ _ _ Hsource _ Hpath) as HsourcePacket.
      pose proof (proj1 (Hseparate _ _ _ _ HsourceCell _ _ HsourcePacket)) as Hapart.
      destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hsource Hpath)
        as [_ [HsourceOffset Hbound]].
      destruct (bytes_path_relative_bound _ _ _ Htotal Hpath) as [HpathDelta Hinside].
      assert (HcellDelta : 0 <= cellDelta <= Ptrofs.max_unsigned).
      { pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)). unfold Ptrofs.max_unsigned; lia. }
      unfold packet_interval_disjoint in *.
      rewrite !Ptrofs.unsigned_repr by assumption.
      rewrite HsourceOffset, HsourceOfs in Hapart.
      pose proof packet_descriptor_size_positive. intuition lia.
  - intros view Hview.
    destruct (fresh_object_copy_packet_view_origin _ _ _ _ _ _ _ _ _ _ _ _
      Hobjects Hsource Hcoverage Hpackets Halign Halloc Hread Hstore _ _ _ Hpacket Hview)
      as [old [old_offset [Hold HoldView]]].
    destruct Hcell as [HoldCell|[Hb HrestCell]].
    + exact (proj2 (Hseparate _ _ _ _ HoldCell _ _ Hold) _ HoldView).
    + subst b. right; left. intro Heq. apply Hfresh. rewrite <- Heq.
      exact (proj1 (proj2 (proj2 (proj2 HoldView)))).
Qed.

Print Assumptions fresh_object_copy_packet_view_origin.
Print Assumptions fresh_object_copy_packet_separation.

Theorem packet_object_coherence_fresh_copy :
  forall ge Sigma m allocated final objects packets source base root fresh bytes,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects source base root ->
  packet_state_valid m packets -> packet_object_coverage ge.(genv_cenv) objects packets ->
  packet_object_coherence ge.(genv_cenv) m objects packets ->
  packet_object_copy_alignment ge.(genv_cenv) root ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) root) = (allocated, fresh) ->
  Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  packet_object_coherence ge.(genv_cenv) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero root)
    (copied_object_packets ge.(genv_cenv) packets root fresh).
Proof.
  intros ge Sigma m allocated final objects packets source base root fresh bytes
    Hobjects Hsource Hv Hcoverage Hcoherent Halign Ha Hr Hw.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Ha) as Hfresh.
  pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
    as [_ [_ [Hextent Hrest]]].
  assert (Htotal : sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus)
    by (pose proof (Ptrofs.unsigned_range base); lia).
  assert (Horigin : forall descriptor offset view,
    copied_object_packets ge.(genv_cenv) packets root fresh descriptor offset ->
    packet_descriptor_valid final descriptor offset view ->
    exists old old_offset, packets old old_offset /\ packet_descriptor_valid m old old_offset view).
  { intros. eapply fresh_object_copy_packet_view_origin; eauto. }
  assert (HobjectFresh : forall b ofs ty, objects b ofs ty -> b <> fresh).
  { intros b ofs ty Hin Heq. subst b. apply Hfresh.
    destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hin) as [_ [_ [_ [Hvalid _]]]]. exact Hvalid. }
  assert (HpacketFresh : forall descriptor offset, packets descriptor offset -> descriptor <> fresh).
  { intros descriptor offset Hin Heq. subst descriptor. apply Hfresh.
    destruct (Hv _ _ Hin) as [_ [v [data [Hd Hdata]]]]. eapply packet_descriptor_source_block; eauto. }
  intros b ofs ty Hobject delta child Hpath descriptor offset Hpacket. split.
  - destruct Hobject as [HoldObject|[Hb [Hofs Hty]]];
      destruct Hpacket as [HoldPacket|[Hdescriptor [leafDelta [Hleaf Hoffset]]]].
    + exact (proj1 (Hcoherent _ _ _ HoldObject _ _ Hpath _ _ HoldPacket)).
    + subst descriptor. left. right; left. intro Heq. symmetry in Heq. eapply HobjectFresh; eauto.
    + subst b ofs ty. left. right; left. eapply HpacketFresh; exact HoldPacket.
    + subst b ofs ty descriptor offset.
      pose proof (Hcoverage _ _ _ Hsource _ Hleaf) as HsourcePacket.
      destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hsource Hleaf)
        as [_ [HsourceOffset Hbound]].
      destruct (bytes_path_relative_bound _ _ _ Htotal Hleaf) as [HleafBounds HleafExtent].
      pose proof (proj1 (Hcoherent _ _ _ Hsource _ _ Hpath _ _ HsourcePacket)) as HsourceShape.
      rewrite Ptrofs.unsigned_zero, Z.add_0_l, Ptrofs.unsigned_repr by exact HleafBounds.
      destruct HsourceShape as [Hapart|[relative [Hrelative [Hsame Hposition]]]].
      * left. unfold packet_interval_disjoint in *.
        rewrite HsourceOffset in Hapart. pose proof packet_descriptor_size_positive. intuition lia.
      * right. exists relative. split; [exact Hrelative|]. split; [reflexivity|].
        rewrite HsourceOffset in Hposition. lia.
  - intros view Hview. destruct (Horigin _ _ _ Hpacket Hview) as [old [old_offset [Hold Hbefore]]].
    destruct Hobject as [HoldObject|[Hb [Hofs Hty]]].
    + exact (proj2 (Hcoherent _ _ _ HoldObject _ _ Hpath _ _ Hold) _ Hbefore).
    + subst b. right; left. intro Heq. apply Hfresh. rewrite <- Heq.
      exact (proj1 (proj2 (proj2 (proj2 Hbefore)))).
Qed.
Print Assumptions packet_object_coherence_fresh_copy.

Theorem fresh_object_copy_packet_heap :
  forall ge Sigma larger m allocated final objects packets cells source base root fresh bytes,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects source base root ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m ->
  packet_heap_invariant ge Sigma m objects cells packets ->
  store_context_extends Sigma larger -> object_type_at ge.(genv_cenv) larger fresh 0 root ->
  packet_object_copy_alignment ge.(genv_cenv) root ->
  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) root) = (allocated, fresh) ->
  Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  packet_heap_invariant ge larger final
    (add_aggregate_descriptor objects fresh Ptrofs.zero root)
    (fresh_copy_layout cells source (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) root) fresh)
    (copied_object_packets ge.(genv_cenv) packets root fresh).
Proof.
  intros ge Sigma larger m allocated final objects packets cells source base root fresh bytes
    Hobjects Hsource Hcells [Hvalid Htyped Hcoverage Hseparation Hcoherent] Hext Hroot Halign Halloc Hread Hstore.
  assert (Htotal : sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus).
  { pose proof (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
      as [_ [_ [Hextent Hrest]]]. pose proof (Ptrofs.unsigned_range base); lia. }
  constructor.
  - eapply fresh_object_copy_packet_state; eauto.
  - eapply copied_object_packets_typed; eauto.
  - apply copied_object_packets_coverage; exact Hcoverage.
  - eapply fresh_object_copy_packet_separation; eauto.
  - eapply packet_object_coherence_fresh_copy; eauto.
Qed.

Print Assumptions fresh_object_copy_packet_heap.
