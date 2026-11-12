(* A byte copy transports actual pointer fragments, including an interior offset.
   This memory regression is independent of the source assignment rules;
   BeePL_aggregate_copy separately checks their progress and preservation. *)
Require Import List ZArith Lia AST Integers Memory Values.
Require Import BeePL_copy_bytes.
Local Open Scope Z_scope.

Theorem pointer_fragment_copy_roundtrip :
  exists target_memory source_memory allocated written copied
    target source destination bytes,
    Mem.alloc Mem.empty 0 8 = (target_memory, target) /\
    Mem.alloc target_memory 0 (size_chunk Mptr) = (source_memory, source) /\
    Mem.alloc source_memory 0 (size_chunk Mptr) = (allocated, destination) /\
    Mem.store Mptr allocated source 0 (Vptr target (Ptrofs.repr 4)) = Some written /\
    Mem.loadbytes written source 0 (size_chunk Mptr) = Some bytes /\
    Mem.storebytes written destination 0 bytes = Some copied /\
    Mem.load Mptr copied destination 0 = Some (Vptr target (Ptrofs.repr 4)) /\
    Ptrofs.repr 4 <> Ptrofs.zero.
Proof.
  destruct (Mem.alloc Mem.empty 0 8) as [target_memory target] eqn:Ht.
  destruct (Mem.alloc target_memory 0 (size_chunk Mptr)) as [source_memory source] eqn:Hs.
  destruct (Mem.alloc source_memory 0 (size_chunk Mptr)) as [allocated destination] eqn:Hd.
  assert (Hsource : Mem.valid_access allocated Mptr source 0 Freeable).
  { eapply Mem.valid_access_alloc_other; [exact Hd |].
    eapply Mem.valid_access_alloc_same; [exact Hs | lia | lia |].
    exists 0; lia. }
  assert (Hdest : Mem.valid_access allocated Mptr destination 0 Freeable).
  { eapply Mem.valid_access_alloc_same; [exact Hd | lia | lia |].
    exists 0; lia. }
  assert (Hwrite : Mem.valid_access allocated Mptr source 0 Writable).
  { eapply Mem.valid_access_implies with (p1 := Freeable); [exact Hsource | constructor]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vptr target (Ptrofs.repr 4)) Hwrite)
    as [written Hstore].
  assert (Hload : Mem.load Mptr written source 0 = Some (Vptr target (Ptrofs.repr 4))).
  { pose proof (Mem.load_store_same _ _ _ _ _ _ Hstore) as H.
    unfold Mptr in *. destruct Archi.ptr64 eqn:Harch;
      simpl in H; rewrite Harch in H; exact H. }
  destruct (Mem.load_loadbytes _ _ _ _ _ Hload) as [bytes [Hbytes Hdecode]].
  assert (Hlength : Z.of_nat (length bytes) = size_chunk Mptr).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hbytes), Z2Nat.id;
      pose proof (size_chunk_pos Mptr); lia. }
  assert (Hdestwritten : Mem.valid_access written Mptr destination 0 Freeable).
  { eapply Mem.store_valid_access_1; eauto. }
  assert (Hrange : Mem.range_perm written destination 0
      (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlength. destruct Hdestwritten as [Hperm _].
    intros ofs Hin. eapply Mem.perm_implies; [apply Hperm; exact Hin | constructor]. }
  destruct (Mem.range_perm_storebytes written destination 0 bytes Hrange) as [copied Hcopy].
  exists target_memory, source_memory, allocated, written, copied,
    target, source, destination, bytes.
  split; [reflexivity |]. split; [exact Hs |]. split; [exact Hd |].
  split; [exact Hstore |]. split; [exact Hbytes |]. split; [exact Hcopy |]. split.
  - change (Mem.load Mptr copied destination (0 + 0) = Some (Vptr target (Ptrofs.repr 4))).
    eapply copied_bytes_scalar_load with (sourceStart := 0) (delta := 0);
      eauto; try lia. exists 0; lia.
  - intro Heq. apply (f_equal Ptrofs.unsigned) in Heq.
    rewrite Ptrofs.unsigned_zero, Ptrofs.unsigned_repr in Heq.
    + discriminate.
    + vm_compute. split; congruence.
Qed.

Print Assumptions pointer_fragment_copy_roundtrip.
