(* Copy initialized scalar leaves using actual CompCert bytes. This preserves
   pointer fragments as well as scalar values; no integer re-encoding occurs. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_copy_bytes.
Local Open Scope Z_scope.

Lemma typed_cell_storebytes_disjoint :
  forall cenv Sigma m m' b ofs ty chunk target start bytes,
  typed_memory_cell cenv Sigma m b ofs ty chunk ->
  Mem.storebytes m target start bytes = Some m' ->
  (b <> target \/ Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= start \/
    start + Z.of_nat (length bytes) <= Ptrofs.unsigned ofs) ->
  typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  intros cenv Sigma m m' b ofs ty chunk target start bytes
    [Hmode Hvolatile Hperm [cv [v [Hload [Hdecode Htyped]]]]] Hstore Haway.
  constructor; try assumption.
  - eapply Mem.storebytes_valid_access_1; eauto.
  - exists cv, v. split.
    + rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore); assumption.
    + split; assumption.
Qed.

Theorem copied_typed_cell :
  forall cenv Sigma L m m' src sourceStart dst destStart count bytes
    delta sourceOffset targetOffset ty chunk,
  Mem.loadbytes m src sourceStart count = Some bytes ->
  Mem.storebytes m dst destStart bytes = Some m' ->
  0 <= delta -> delta + size_chunk (transl_bchunk_cchunk chunk) <= count ->
  Ptrofs.unsigned sourceOffset = sourceStart + delta ->
  Ptrofs.unsigned targetOffset = destStart + delta ->
  Mem.valid_access m (transl_bchunk_cchunk chunk) dst
    (Ptrofs.unsigned targetOffset) Freeable ->
  typed_memory_cell cenv Sigma m src sourceOffset ty chunk ->
  (forall v, deref_addr ty m src sourceOffset Full v -> value_locations L v ty) ->
  typed_memory_cell cenv Sigma m' dst targetOffset ty chunk /\
  (forall v, deref_addr ty m' dst targetOffset Full v -> value_locations L v ty).
Proof.
  intros cenv Sigma L m m' src sourceStart dst destStart count bytes
    delta sourceOffset targetOffset ty chunk Hbytes Hstore Hdelta Hbound
    Hsource Htarget HtargetPerm Hcell Hlocations.
  destruct Hcell as [Hmode Hvolatile HsourcePerm [cv [v [Hload [Hdecode Htyped]]]]].
  assert (Hcopied : Mem.load (transl_bchunk_cchunk chunk) m' dst
    (Ptrofs.unsigned targetOffset) = Some cv).
  { rewrite Htarget. eapply copied_bytes_scalar_load; eauto.
    - destruct HtargetPerm as [_ Halign]. rewrite Htarget in Halign. exact Halign.
    - rewrite <- Hsource. exact Hload. }
  assert (Hresult : typed_memory_cell cenv Sigma m' dst targetOffset ty chunk).
  { constructor; try assumption.
    - eapply Mem.storebytes_valid_access_1; eauto.
    - exists cv, v. repeat split; assumption. }
  split; [exact Hresult |]. intros actual Hread.
  assert (Hreadv : deref_addr ty m' dst targetOffset Full v).
  { eapply deref_addr_value; eauto. }
  assert (actual = v) by (eapply deref_full_deterministic; eauto).
  subst actual. apply Hlocations. eapply deref_addr_value; eauto.
Qed.

(* A copy plan covers each successor scalar cell either by an unchanged old
   cell, or by a corresponding initialized source leaf. It contains no
   assumptions about successor contents. Object-layout construction must
   supply this plan and destination permissions before executing the copy. *)
Definition scalar_copy_plan (before after : scalar_layout)
    (src : Values.block) (sourceStart : Z) (dst : Values.block)
    (destStart count : Z) : Prop :=
  forall b ofs ty chunk, after b ofs ty chunk ->
    (before b ofs ty chunk /\
      (b <> dst \/ Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= destStart \/
        destStart + count <= Ptrofs.unsigned ofs)) \/
    (b = dst /\ exists delta sourceOffset,
      before src sourceOffset ty chunk /\
      0 <= delta /\ delta + size_chunk (transl_bchunk_cchunk chunk) <= count /\
      Ptrofs.unsigned sourceOffset = sourceStart + delta /\
      Ptrofs.unsigned ofs = destStart + delta /\
      (align_chunk (transl_bchunk_cchunk chunk) | Ptrofs.unsigned ofs)).

Theorem typed_located_layout_copy :
  forall cenv Sigma L before after m m' src sourceStart dst destStart count bytes,
  0 <= count ->
  Mem.loadbytes m src sourceStart count = Some bytes ->
  Mem.storebytes m dst destStart bytes = Some m' ->
  Mem.range_perm m dst destStart (destStart + count) Cur Freeable ->
  typed_memory_layout cenv Sigma before m -> memory_locations L before m ->
  scalar_copy_plan before after src sourceStart dst destStart count ->
  typed_memory_layout cenv Sigma after m' /\ memory_locations L after m'.
Proof.
  intros cenv Sigma L before after m m' src sourceStart dst destStart count bytes
    Hcount Hbytes Hstore Hwrite Htyped Hlocated Hplan.
  assert (Hlength : Z.of_nat (length bytes) = count).
  { pose proof (Mem.loadbytes_length _ _ _ _ _ Hbytes) as Hlen.
    rewrite Hlen. apply Z2Nat.id; exact Hcount. }
  assert (Hcells : forall b ofs ty chunk, after b ofs ty chunk ->
    typed_memory_cell cenv Sigma m' b ofs ty chunk /\
    (forall v, deref_addr ty m' b ofs Full v -> value_locations L v ty)).
  { intros b ofs ty chunk Hentry.
    destruct (Hplan b ofs ty chunk Hentry) as [[Hold Haway] |
      [Hb [delta [sourceOffset [Hsource [Hdelta [Hbound [Hsrc [Hdst Halign]]]]]]]]].
    - assert (Hcell := Htyped b ofs ty chunk Hold).
      assert (HawayBytes : b <> dst \/
        Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= destStart \/
        destStart + Z.of_nat (length bytes) <= Ptrofs.unsigned ofs).
      { rewrite Hlength. exact Haway. }
      split; [eapply typed_cell_storebytes_disjoint; eauto |].
      intros actual Hread.
      destruct Hcell as [Hmode Hvolatile Hperm [cv [v [Hload [Hdecode Hv]]]]].
      assert (Hreadv : deref_addr ty m' b ofs Full v).
      { eapply deref_addr_value with (chunk := chunk) (v := cv);
          [exact Hmode | exact Hvolatile | | exact Hdecode].
        simpl. rewrite (Mem.load_storebytes_other _ _ _ _ _ Hstore); assumption. }
      assert (actual = v) by (eapply deref_full_deterministic; eauto).
      subst actual. eapply Hlocated; [exact Hold |]. eapply deref_addr_value; eauto.
    - subst b. eapply copied_typed_cell; eauto.
      split; [|exact Halign]. intros offset Hin.
      apply Hwrite. rewrite Hdst in Hin. lia. }
  split.
  - intros b ofs ty chunk Hentry. exact (proj1 (Hcells b ofs ty chunk Hentry)).
  - intros b ofs ty chunk Hentry v Hread.
    exact (proj2 (Hcells b ofs ty chunk Hentry) v Hread).
Qed.

Print Assumptions copied_typed_cell.
Print Assumptions typed_located_layout_copy.
