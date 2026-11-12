(* Packet state tracks descriptor locations, not immutable endpoint values.
   A copy may replace the view at a location; validity is re-established from
   actual memory operations. This invariant is separate from scalar layouts. *)
Require Import List ZArith Lia Integers AST Maps Memory.
Require Import BeeTypes BeePL BeePL_packet BeePL_packet_descriptor_copy.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_locations := Values.block -> ptrofs -> Prop.

Definition packet_state_valid (m : Mem.mem) (locations : packet_locations) : Prop :=
  forall descriptor offset, locations descriptor offset ->
  Ptrofs.unsigned offset + packet_descriptor_size <= Ptrofs.modulus /\
  exists view bytes,
    packet_descriptor_valid m descriptor offset view /\
    Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first))
      (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) = Some bytes /\
    initialized_packet_contents bytes.

Definition packet_state_typed cenv Sigma (locations : packet_locations) : Prop :=
  forall descriptor offset, locations descriptor offset ->
    object_type_at cenv Sigma descriptor (Ptrofs.unsigned offset) Bytes.

Definition packet_interval_disjoint (block : Values.block) (start size : Z)
    (written : Values.block) (target count : Z) : Prop :=
  size = 0 \/ block <> written \/ start + size <= target \/ target + count <= start.

Definition packet_write_separated m (locations : packet_locations)
    (written : Values.block) (target count : Z) : Prop :=
  forall descriptor offset, locations descriptor offset ->
    packet_interval_disjoint descriptor (Ptrofs.unsigned offset) packet_descriptor_size written target count /\
    forall view, packet_descriptor_valid m descriptor offset view ->
      packet_interval_disjoint view.(packet_block) (Ptrofs.unsigned view.(packet_first))
        (Ptrofs.unsigned view.(packet_last) - Ptrofs.unsigned view.(packet_first)) written target count.

Lemma packet_state_valid_subcontext : forall m locations smaller,
  packet_state_valid m locations ->
  (forall b ofs, smaller b ofs -> locations b ofs) -> packet_state_valid m smaller.
Proof. unfold packet_state_valid; eauto. Qed.

Lemma packet_descriptor_store_frame : forall m final chunk written target value descriptor offset view,
  Mem.store chunk m written target value = Some final ->
  packet_interval_disjoint descriptor (Ptrofs.unsigned offset) packet_descriptor_size
    written target (size_chunk chunk) ->
  packet_descriptor_valid m descriptor offset view ->
  packet_descriptor_valid final descriptor offset view.
Proof.
  intros m final chunk written target value descriptor offset view Hstore Hapart [Hfirst [Hlast Hview]].
  pose proof packet_descriptor_size_positive as Hpositive.
  pose proof (size_chunk_pos Mptr) as Hpointer.
  unfold packet_interval_disjoint in Hapart. unfold packet_descriptor_size in Hapart, Hpositive.
  split.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (intuition lia). exact Hfirst.
  - split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore) by (intuition lia). exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.store_valid_block_1; eauto.
      * intros; eapply Mem.perm_store_1; eauto.
Qed.

Theorem packet_state_store_preserved : forall m final locations chunk written target value,
  packet_state_valid m locations ->
  packet_write_separated m locations written target (size_chunk chunk) ->
  Mem.store chunk m written target value = Some final ->
  packet_state_valid final locations.
Proof.
  intros m final locations chunk written target value Hvalid Hseparate Hstore descriptor offset Hentry.
  destruct (Hvalid _ _ Hentry) as [Hbound [view [bytes [Hdescriptor [Hbytes Hinitialized]]]]].
  destruct (Hseparate _ _ Hentry) as [Hapart Hregion].
  specialize (Hregion _ Hdescriptor).
  split; [exact Hbound|]. exists view, bytes. split.
  - eapply packet_descriptor_store_frame; eauto.
  - split; [|exact Hinitialized].
    rewrite (Mem.loadbytes_store_other _ _ _ _ _ _ Hstore).
    + exact Hbytes.
    + unfold packet_interval_disjoint in Hregion. intuition lia.
Qed.

Theorem packet_state_storebytes_preserved : forall m final locations written target bytes,
  packet_state_valid m locations ->
  packet_write_separated m locations written target (Z.of_nat (length bytes)) ->
  Mem.storebytes m written target bytes = Some final ->
  packet_state_valid final locations.
Proof.
  intros m final locations written target bytes Hvalid Hseparate Hstore descriptor offset Hentry.
  destruct (Hvalid _ _ Hentry) as [Hbound [view [contents [Hdescriptor [Hbytes Hinitialized]]]]].
  destruct (Hseparate _ _ Hentry) as [Hapart Hregion].
  specialize (Hregion _ Hdescriptor).
  pose proof (proj1 (proj2 (proj2 Hdescriptor))) as Horder.
  split; [exact Hbound|]. exists view, contents. split.
  - eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |exact Hdescriptor].
    unfold packet_interval_disjoint in Hapart. pose proof packet_descriptor_size_positive. intuition lia.
  - split; [|exact Hinitialized].
    unfold packet_interval_disjoint in Hregion.
    destruct Hregion as [Hzero|Hregion].
    + rewrite Hzero in *. rewrite Mem.loadbytes_empty in * by lia; exact Hbytes.
    + rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore); [exact Hbytes|lia|exact Hregion].
Qed.

Definition extend_packet_locations (locations : packet_locations) (fresh : Values.block)
    (offset : ptrofs) : packet_locations :=
  fun b ofs => locations b ofs \/ (b = fresh /\ ofs = offset).

Theorem packet_state_fresh_descriptor_copy : forall m locations src source,
  packet_state_valid m locations -> locations src source ->
  exists allocated fresh bytes final,
    Mem.alloc m 0 packet_descriptor_size = (allocated, fresh) /\
    Mem.loadbytes allocated src (Ptrofs.unsigned source) packet_descriptor_size = Some bytes /\
    Mem.storebytes allocated fresh 0 bytes = Some final /\
    ~ Mem.valid_block m fresh /\
    packet_state_valid final (extend_packet_locations locations fresh Ptrofs.zero) /\
    (forall old offset count, Mem.valid_block m old -> 0 <= count ->
      Mem.loadbytes final old offset count = Mem.loadbytes m old offset count).
Proof.
  intros m locations src source Hstate Hsource.
  destruct (Hstate _ _ Hsource) as [HsourceBound [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
  destruct (fresh_packet_descriptor_copy _ _ _ _ Hdescriptor)
    as [allocated [fresh [bytes [final [Halloc [Hread [Hstore [Hnew [Hfresh [Hframe Hdescriptors]]]]]]]]]].
  exists allocated, fresh, bytes, final. split; [exact Halloc|]. split; [exact Hread|].
  split; [exact Hstore|]. split; [exact Hfresh|]. split; [|exact Hframe].
  intros descriptor offset [Hold|[Heqb Heqo]].
  - destruct (Hstate _ _ Hold) as [HoldBound [oldview [oldcontents [HoldDescriptor [HoldBytes HoldInitialized]]]]].
    split; [exact HoldBound|]. exists oldview, oldcontents. split; [apply Hdescriptors; exact HoldDescriptor|].
    split; [|exact HoldInitialized].
    destruct HoldDescriptor as [_ [_ [Horder [Hblock Hrange]]]].
    rewrite Hframe by (assumption || lia). exact HoldBytes.
  - subst descriptor offset. split.
    { rewrite Ptrofs.unsigned_zero. unfold packet_descriptor_size. vm_compute; congruence. }
    exists view, contents. split; [exact Hnew|]. split; [|exact Hinitialized].
    destruct Hdescriptor as [_ [_ [Horder [Hblock Hrange]]]].
    rewrite Hframe by (assumption || lia). exact Hcontents.
Qed.

(* Empty packet intervals are valid, including one-past-end endpoints; no
   dereferenceability premise is imposed on packet_last itself. *)
Lemma packet_state_empty_view : forall m locations,
  (forall descriptor offset, locations descriptor offset ->
    Ptrofs.unsigned offset + packet_descriptor_size <= Ptrofs.modulus /\
    exists block endpoint,
      packet_descriptor_valid m descriptor offset
        {| packet_block := block; packet_first := endpoint; packet_last := endpoint |}) ->
  packet_state_valid m locations.
Proof.
  intros m locations Hviews descriptor offset Hentry.
  destruct (Hviews _ _ Hentry) as [Hbound [block [endpoint Hdescriptor]]].
  split; [exact Hbound|].
  exists {| packet_block := block; packet_first := endpoint; packet_last := endpoint |}, [].
  split; [exact Hdescriptor|]. split.
  - simpl. rewrite Z.sub_diag. apply Mem.loadbytes_empty; lia.
  - exists []; reflexivity.
Qed.

Print Assumptions packet_state_store_preserved.
Print Assumptions packet_state_storebytes_preserved.
Print Assumptions packet_state_fresh_descriptor_copy.
