(* A concrete copy plan for a zero-based array of primitive elements. This
   covers bool and all integer widths, not arbitrary aggregate element types. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_array_proofs.
Require Import BeePL_copy_cells.
Local Open Scope Z_scope.

Theorem primitive_array_fresh_copy_plan :
  forall cenv Sigma before m allocated src fresh pt count,
  typed_memory_layout cenv Sigma before m ->
  Mem.alloc m 0 (sizeof_ptype pt * Z.of_nat count) = (allocated, fresh) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  (forall i, (i < count)%nat ->
    before src (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt))
      (Vtype pt) (chunk_of_ptype pt)) ->
  scalar_copy_plan before (extend_array_layout before fresh pt count)
    src 0 fresh 0 (sizeof_ptype pt * Z.of_nat count).
Proof.
  intros cenv Sigma before m allocated src fresh pt count Hmemory Halloc Hextent Hsource.
  intros b ofs ty chunk [Hold | [i [Hi [Hb [Hofs [Hty Hchunk]]]]]].
  - left. split; [exact Hold |]. left. intro Heq. subst b.
    assert (Hvalid : Mem.valid_block m fresh).
    { eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure.
      apply Hmemory; exact Hold. }
    eapply Mem.fresh_block_alloc; eauto.
  - subst b ofs ty chunk. right. split; [reflexivity |].
    exists (Z.of_nat i * sizeof_ptype pt), (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt)).
    pose proof (primitive_size_positive pt) as Hwidth.
    assert (Hindex : Z.of_nat i < Z.of_nat count) by (apply Nat2Z.inj_lt; exact Hi).
    assert (Hoffset : 0 <= Z.of_nat i * sizeof_ptype pt <= Ptrofs.max_unsigned) by nia.
    split; [apply Hsource; exact Hi |]. split; [nia |]. split.
    + rewrite primitive_chunk_size. nia.
    + rewrite Ptrofs.unsigned_repr by exact Hoffset.
      split; [lia |]. split; [lia |]. rewrite primitive_chunk_alignment.
      exists (Z.of_nat i). reflexivity.
Qed.

(* Canonical source layouts are a convenient specialization. The old layout
   must already contain the source cells with actual typed contents. *)
Corollary canonical_primitive_array_fresh_copy_plan :
  forall cenv Sigma old m allocated src fresh pt count,
  typed_memory_layout cenv Sigma (extend_array_layout old src pt count) m ->
  Mem.alloc m 0 (sizeof_ptype pt * Z.of_nat count) = (allocated, fresh) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  scalar_copy_plan (extend_array_layout old src pt count)
    (extend_array_layout (extend_array_layout old src pt count) fresh pt count)
    src 0 fresh 0 (sizeof_ptype pt * Z.of_nat count).
Proof.
  intros cenv Sigma old m allocated src fresh pt count Hmemory Halloc Hextent.
  eapply primitive_array_fresh_copy_plan; [exact Hmemory | exact Halloc | exact Hextent |].
  intros i Hi. right. exists i. repeat split; auto.
Qed.

Print Assumptions primitive_array_fresh_copy_plan.
Print Assumptions canonical_primitive_array_fresh_copy_plan.
