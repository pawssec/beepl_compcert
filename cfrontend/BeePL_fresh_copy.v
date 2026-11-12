(* Copying into freshly allocated storage derives the frame condition from
   allocation freshness. Relative leaf alignment is supplied by object layout. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_copy_cells BeePL_aggregate_copy.
Local Open Scope Z_scope.

Definition fresh_copy_layout (before : scalar_layout) (src : Values.block)
    (sourceStart count : Z) (fresh : Values.block) : scalar_layout :=
  fun b ofs ty chunk => before b ofs ty chunk \/
    (b = fresh /\ exists sourceOffset delta,
      before src sourceOffset ty chunk /\
      Ptrofs.unsigned sourceOffset = sourceStart + delta /\
      0 <= delta /\ delta + size_chunk (transl_bchunk_cchunk chunk) <= count /\
      ofs = Ptrofs.repr delta).

Definition relative_copy_alignment (before : scalar_layout)
    (src : Values.block) (sourceStart count : Z) : Prop :=
  forall sourceOffset ty chunk delta,
    before src sourceOffset ty chunk ->
    Ptrofs.unsigned sourceOffset = sourceStart + delta ->
    0 <= delta -> delta + size_chunk (transl_bchunk_cchunk chunk) <= count ->
    (align_chunk (transl_bchunk_cchunk chunk) | delta).

Lemma zero_based_copy_alignment : forall cenv Sigma before m src count,
  typed_memory_layout cenv Sigma before m ->
  relative_copy_alignment before src 0 count.
Proof.
  intros cenv Sigma before m src count Htyped ofs ty chunk delta Hentry Hoffset Hdelta Hbound.
  pose proof (typed_cell_permission _ _ _ _ _ _ _ (Htyped _ _ _ _ Hentry)) as Hperm.
  destruct Hperm as [_ Halign]. rewrite Hoffset in Halign. exact Halign.
Qed.

Lemma fresh_copy_layout_extends : forall before src sourceStart count fresh,
  forall b ofs ty chunk, before b ofs ty chunk ->
    fresh_copy_layout before src sourceStart count fresh b ofs ty chunk.
Proof. intros. left; assumption. Qed.

Theorem allocated_fresh_copy_plan :
  forall cenv Sigma before m allocated fresh src sourceStart count,
  typed_memory_layout cenv Sigma before m ->
  Mem.alloc m 0 count = (allocated, fresh) -> count <= Ptrofs.modulus ->
  relative_copy_alignment before src sourceStart count ->
  scalar_copy_plan before (fresh_copy_layout before src sourceStart count fresh)
    src sourceStart fresh 0 count.
Proof.
  intros cenv Sigma before m allocated fresh src sourceStart count
    Htyped Halloc Hcount Halign b ofs ty chunk Hentry.
  destruct Hentry as [Hold | [Hb [sourceOffset [delta [Hsource [Hoffset [Hdelta [Hbound Hofs]]]]]]]].
  - left. split; [exact Hold |]. left. intro Heq. subst b.
    eapply Mem.fresh_block_alloc; [exact Halloc |].
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure.
    apply Htyped; exact Hold.
  - subst b ofs. right. split; [reflexivity |]. exists delta, sourceOffset.
    assert (Hrepr : Ptrofs.unsigned (Ptrofs.repr delta) = delta).
    { apply Ptrofs.unsigned_repr. pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
      unfold Ptrofs.max_unsigned. lia. }
    split; [exact Hsource |]. split; [exact Hdelta |]. split; [exact Hbound |].
    split; [exact Hoffset |]. rewrite Hrepr. split; [lia |]. eapply Halign; eauto.
Qed.

Lemma allocation_memory_locations : forall cenv Sigma L before m allocated fresh lo hi,
  typed_memory_layout cenv Sigma before m -> memory_locations L before m ->
  Mem.alloc m lo hi = (allocated, fresh) -> memory_locations L before allocated.
Proof.
  intros cenv Sigma L before m allocated fresh lo hi Htyped Hlocated Halloc
    b ofs ty chunk Hentry actual Hread.
  destruct (Htyped b ofs ty chunk Hentry)
    as [Hmode Hvolatile Hperm [cv [v [Hload [Hdecode Hv]]]]].
  assert (Hreadv : deref_addr ty allocated b ofs Full v).
  { eapply deref_addr_value with (chunk := chunk) (v := cv);
      [exact Hmode | exact Hvolatile | | exact Hdecode].
    simpl. eapply Mem.load_alloc_other; eauto. }
  assert (actual = v) by (eapply deref_full_deterministic; eauto).
  subst actual. eapply Hlocated; [exact Hentry |]. eapply deref_addr_value; eauto.
Qed.

Theorem fresh_copy_preserves_cells :
  forall cenv Sigma L before m allocated final fresh src sourceStart count bytes,
  typed_memory_layout cenv Sigma before m -> memory_locations L before m ->
  Mem.alloc m 0 count = (allocated, fresh) ->
  0 <= count <= Ptrofs.modulus ->
  relative_copy_alignment before src sourceStart count ->
  Mem.loadbytes allocated src sourceStart count = Some bytes ->
  Mem.storebytes allocated fresh 0 bytes = Some final ->
  typed_memory_layout cenv Sigma
    (fresh_copy_layout before src sourceStart count fresh) final /\
  memory_locations L (fresh_copy_layout before src sourceStart count fresh) final.
Proof.
  intros cenv Sigma L before m allocated final fresh src sourceStart count bytes
    Htyped Hlocated Halloc [Hnonnegative Hbound] Halign Hbytes Hstore.
  eapply (typed_located_layout_copy cenv Sigma L before
    (fresh_copy_layout before src sourceStart count fresh)
    allocated final src sourceStart fresh 0 count bytes);
    [exact Hnonnegative | exact Hbytes | exact Hstore | | | |].
  - intros offset Hin. eapply Mem.perm_alloc_2; eauto.
  - intros b ofs ty chunk Hentry. eapply typed_memory_cell_alloc_frame; eauto.
  - eapply allocation_memory_locations; eauto.
  - eapply allocated_fresh_copy_plan; eauto.
Qed.

Print Assumptions allocated_fresh_copy_plan.
Print Assumptions fresh_copy_preserves_cells.
