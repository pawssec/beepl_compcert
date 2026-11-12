(* Byte copies retain CompCert memory values, including pointer fragments.
   No integer re-encoding of pointer payloads is involved. *)
Require Import List ZArith Lia Coqlib AST Memory Memdata Values.
Import ListNotations.
Local Open Scope Z_scope.

Lemma equal_loaded_bytes_subrange :
  forall m1 b1 start1 m2 b2 start2 total bytes delta count,
  Mem.loadbytes m1 b1 start1 total = Some bytes ->
  Mem.loadbytes m2 b2 start2 total = Some bytes ->
  0 <= delta -> 0 <= count -> delta + count <= total ->
  exists part,
    Mem.loadbytes m1 b1 (start1 + delta) count = Some part /\
    Mem.loadbytes m2 b2 (start2 + delta) count = Some part.
Proof.
  intros m1 b1 start1 m2 b2 start2 total bytes delta count
    Hfirst Hsecond Hdelta Hcount Hbound.
  assert (Htotal : total = delta + (total - delta)) by lia.
  rewrite Htotal in Hfirst, Hsecond.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ Hfirst ltac:(lia) ltac:(lia))
    as [prefix1 [tail1 [Hprefix1 [Htail1 Heq1]]]].
  destruct (Mem.loadbytes_split _ _ _ _ _ _ Hsecond ltac:(lia) ltac:(lia))
    as [prefix2 [tail2 [Hprefix2 [Htail2 Heq2]]]].
  assert (Hprefixlen : length prefix1 = length prefix2).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hprefix1),
      (Mem.loadbytes_length _ _ _ _ _ Hprefix2). reflexivity. }
  destruct (@list_append_injective_l memval prefix1 tail1 prefix2 tail2 ltac:(congruence) Hprefixlen)
    as [_ Htails]. subst tail2.
  assert (Hrest : total - delta = count + (total - delta - count)) by lia.
  rewrite Hrest in Htail1, Htail2.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ Htail1 ltac:(lia) ltac:(lia))
    as [part1 [suffix1 [Hpart1 [Hsuffix1 Hparts1]]]].
  destruct (Mem.loadbytes_split _ _ _ _ _ _ Htail2 ltac:(lia) ltac:(lia))
    as [part2 [suffix2 [Hpart2 [Hsuffix2 Hparts2]]]].
  assert (Hpartlen : length part1 = length part2).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hpart1),
      (Mem.loadbytes_length _ _ _ _ _ Hpart2). reflexivity. }
  destruct (@list_append_injective_l memval part1 suffix1 part2 suffix2 ltac:(congruence) Hpartlen)
    as [Hparts _]. subst part2. exists part1. split; assumption.
Qed.

Theorem copied_bytes_scalar_load :
  forall m m' src sourceStart dst destStart total bytes delta chunk cv,
  Mem.loadbytes m src sourceStart total = Some bytes ->
  Mem.storebytes m dst destStart bytes = Some m' ->
  0 <= delta -> delta + size_chunk chunk <= total ->
  (align_chunk chunk | destStart + delta) ->
  Mem.load chunk m src (sourceStart + delta) = Some cv ->
  Mem.load chunk m' dst (destStart + delta) = Some cv.
Proof.
  intros m m' src sourceStart dst destStart total bytes delta chunk cv
    Hloadbytes Hstore Hdelta Hbound Halign Hload.
  assert (Hcount : 0 <= size_chunk chunk) by (pose proof (size_chunk_pos chunk); lia).
  assert (Hlength : Z.of_nat (length bytes) = total).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hloadbytes). rewrite Z2Nat.id; lia. }
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Hstore) as Hcopied.
  rewrite Hlength in Hcopied.
  destruct (equal_loaded_bytes_subrange _ _ _ _ _ _ _ _ _ _
    Hloadbytes Hcopied Hdelta Hcount Hbound) as [part [Hsource Hdest]].
  destruct (Mem.load_loadbytes _ _ _ _ _ Hload) as [sourcepart [Hsourcepart Hdecode]].
  assert (sourcepart = part) by congruence. subst sourcepart cv.
  apply Mem.loadbytes_load; assumption.
Qed.

Print Assumptions equal_loaded_bytes_subrange.
Print Assumptions copied_bytes_scalar_load.
