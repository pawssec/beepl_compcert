(* Bytes copies duplicate the two-pointer descriptor, not packet payload bytes.
   The pointer-fragment copy lemma preserves provenance exactly. *)
Require Import List ZArith Lia Integers AST Memory.
Require Import BeePL_packet BeePL_packet_proofs BeePL_copy_bytes.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_descriptor_size : Z := 2 * size_chunk Mptr.

Lemma packet_descriptor_size_positive : 0 < packet_descriptor_size.
Proof. unfold packet_descriptor_size. pose proof (size_chunk_pos Mptr); lia. Qed.

Lemma pointer_slot_alignment : (align_chunk Mptr | size_chunk Mptr).
Proof. exists 1. reflexivity. Qed.

Lemma packet_view_valid_frame : forall m m' view,
  packet_view_valid m view ->
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  packet_view_valid m' view.
Proof.
  intros m m' view [Horder [Hblock Hrange]] Hblocks Hperms.
  split; [exact Horder|]. split; [auto|]. intros ofs Hin. eapply Hperms; eauto.
Qed.

Lemma packet_descriptor_source_block : forall m descriptor offset view,
  packet_descriptor_valid m descriptor offset view -> Mem.valid_block m descriptor.
Proof.
  intros m descriptor offset view [Hfirst _].
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies with (p1 := Readable); [|constructor].
  eapply Mem.load_valid_access; exact Hfirst.
Qed.

Lemma packet_descriptor_loadbytes : forall m descriptor offset view,
  packet_descriptor_valid m descriptor offset view ->
  exists bytes, Mem.loadbytes m descriptor (Ptrofs.unsigned offset) packet_descriptor_size = Some bytes.
Proof.
  intros m descriptor offset view [Hfirst [Hlast Hview]].
  pose proof (Mem.load_valid_access _ _ _ _ _ Hfirst) as [HfirstPerm HfirstAlign].
  pose proof (Mem.load_valid_access _ _ _ _ _ Hlast) as [HlastPerm HlastAlign].
  apply Mem.range_perm_loadbytes. intros position Hat. unfold packet_descriptor_size in Hat.
  destruct (Z_lt_dec position (Ptrofs.unsigned offset + size_chunk Mptr)).
  - apply HfirstPerm; lia.
  - apply HlastPerm; lia.
Qed.

Lemma copied_packet_descriptor_valid : forall m final src source dst target view bytes,
  packet_descriptor_valid m src source view ->
  Mem.loadbytes m src (Ptrofs.unsigned source) packet_descriptor_size = Some bytes ->
  Mem.storebytes m dst (Ptrofs.unsigned target) bytes = Some final ->
  (align_chunk Mptr | Ptrofs.unsigned target) ->
  packet_descriptor_valid final dst target view.
Proof.
  intros m final src source dst target view bytes [Hfirst [Hlast Hview]] Hread Hwrite Halign.
  assert (Hsize : 0 < size_chunk Mptr) by (pose proof (size_chunk_pos Mptr); lia).
  split.
  - replace (Ptrofs.unsigned target) with (Ptrofs.unsigned target + 0) by lia.
    eapply copied_bytes_scalar_load with (delta := 0) (total := packet_descriptor_size); eauto;
      unfold packet_descriptor_size; try lia.
    + replace (Ptrofs.unsigned target + 0) with (Ptrofs.unsigned target) by lia; exact Halign.
    + replace (Ptrofs.unsigned source + 0) with (Ptrofs.unsigned source) by lia; exact Hfirst.
  - split.
    + eapply copied_bytes_scalar_load with (delta := size_chunk Mptr)
        (total := packet_descriptor_size); eauto; unfold packet_descriptor_size; try lia.
      apply Z.divide_add_r; [exact Halign|apply pointer_slot_alignment].
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Theorem packet_descriptor_copy_into : forall m src source dst target view,
  packet_descriptor_valid m src source view ->
  Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target + packet_descriptor_size) Cur Writable ->
  (align_chunk Mptr | Ptrofs.unsigned target) ->
  exists bytes final,
    Mem.loadbytes m src (Ptrofs.unsigned source) packet_descriptor_size = Some bytes /\
    Mem.storebytes m dst (Ptrofs.unsigned target) bytes = Some final /\
    packet_descriptor_valid final dst target view.
Proof.
  intros m src source dst target view Hdescriptor Hwrite Halign.
  destruct (packet_descriptor_loadbytes _ _ _ _ Hdescriptor) as [bytes Hread].
  assert (Hlength : Z.of_nat (length bytes) = packet_descriptor_size).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hread), Z2Nat.id;
      pose proof packet_descriptor_size_positive; lia. }
  destruct (Mem.range_perm_storebytes m dst (Ptrofs.unsigned target) bytes
    ltac:(rewrite Hlength; exact Hwrite)) as [final Hstore].
  exists bytes, final. split; [exact Hread|]. split; [exact Hstore|].
  eapply copied_packet_descriptor_valid; eauto.
Qed.

Lemma packet_descriptor_alloc_frame : forall m allocated fresh lo hi descriptor offset view,
  Mem.alloc m lo hi = (allocated, fresh) ->
  packet_descriptor_valid m descriptor offset view ->
  packet_descriptor_valid allocated descriptor offset view.
Proof.
  intros m allocated fresh lo hi descriptor offset view Halloc Hvalid.
  pose proof (packet_descriptor_source_block _ _ _ _ Hvalid) as Hblock.
  destruct Hvalid as [Hfirst [Hlast Hview]]. split.
  - rewrite (Mem.load_alloc_unchanged _ _ _ _ _ Halloc) by exact Hblock. exact Hfirst.
  - split.
    + rewrite (Mem.load_alloc_unchanged _ _ _ _ _ Halloc) by exact Hblock. exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.valid_block_alloc; eauto.
      * intros; eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma packet_descriptor_storebytes_disjoint : forall m final dst start bytes descriptor offset view,
  Mem.storebytes m dst start bytes = Some final ->
  (descriptor <> dst \/ Ptrofs.unsigned offset + packet_descriptor_size <= start \/
    start + Z.of_nat (length bytes) <= Ptrofs.unsigned offset) ->
  packet_descriptor_valid m descriptor offset view ->
  packet_descriptor_valid final descriptor offset view.
Proof.
  intros m final dst start bytes descriptor offset view Hstore Hapart [Hfirst [Hlast Hview]].
  pose proof (size_chunk_pos Mptr) as Hsize.
  unfold packet_descriptor_size in Hapart. split.
  - rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore) by (intuition lia). exact Hfirst.
  - split.
    + rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore) by (intuition lia). exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma packet_descriptor_storebytes_frame : forall m final dst start bytes descriptor offset view,
  Mem.storebytes m dst start bytes = Some final ->
  descriptor <> dst -> packet_descriptor_valid m descriptor offset view ->
  packet_descriptor_valid final descriptor offset view.
Proof.
  intros m final dst start bytes descriptor offset view Hstore Hapart [Hfirst [Hlast Hview]].
  split.
  - rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore) by auto. exact Hfirst.
  - split.
    + rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore) by auto. exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Theorem fresh_packet_descriptor_copy : forall m src source view,
  packet_descriptor_valid m src source view ->
  exists allocated fresh bytes final,
    Mem.alloc m 0 packet_descriptor_size = (allocated, fresh) /\
    Mem.loadbytes allocated src (Ptrofs.unsigned source) packet_descriptor_size = Some bytes /\
    Mem.storebytes allocated fresh 0 bytes = Some final /\
    packet_descriptor_valid final fresh Ptrofs.zero view /\
    ~ Mem.valid_block m fresh /\
    (forall old offset count, Mem.valid_block m old -> 0 <= count ->
      Mem.loadbytes final old offset count = Mem.loadbytes m old offset count) /\
    (forall old offset oldview, packet_descriptor_valid m old offset oldview ->
      packet_descriptor_valid final old offset oldview).
Proof.
  intros m src source view Hdescriptor.
  destruct (Mem.alloc m 0 packet_descriptor_size) as [allocated fresh] eqn:Halloc.
  assert (Hsource : packet_descriptor_valid allocated src source view).
  { eapply packet_descriptor_alloc_frame; eauto. }
  assert (Hwrite : Mem.range_perm allocated fresh (Ptrofs.unsigned Ptrofs.zero)
    (Ptrofs.unsigned Ptrofs.zero + packet_descriptor_size) Cur Writable).
  { rewrite Ptrofs.unsigned_zero. intros position Hat. eapply Mem.perm_implies.
    - eapply Mem.perm_alloc_2; [exact Halloc|lia].
    - constructor. }
  destruct (packet_descriptor_copy_into allocated src source fresh Ptrofs.zero view Hsource Hwrite
    ltac:(rewrite Ptrofs.unsigned_zero; exists 0; reflexivity)) as [bytes [final [Hread [Hstore Hvalid]]]].
  rewrite Ptrofs.unsigned_zero in Hstore.
  assert (Hfresh : ~ Mem.valid_block m fresh) by (eapply Mem.fresh_block_alloc; eauto).
  exists allocated, fresh, bytes, final. split; [reflexivity|].
  split; [exact Hread|]. split; [exact Hstore|]. split; [exact Hvalid|]. split; [exact Hfresh|].
  split.
  - intros old offset count Hold Hcount.
    assert (Hapart : old <> fresh) by (intro Heq; subst; contradiction).
    rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore old offset count) by (auto; lia).
    eapply Mem.loadbytes_alloc_unchanged; eauto.
  - intros old offset oldview Hold.
    assert (Hapart : old <> fresh).
    { intro Heq; subst. apply Hfresh. eapply packet_descriptor_source_block; eauto. }
    eapply packet_descriptor_storebytes_frame; [exact Hstore|exact Hapart|].
    eapply packet_descriptor_alloc_frame; eauto.
Qed.

Print Assumptions packet_descriptor_copy_into.
Print Assumptions fresh_packet_descriptor_copy.
