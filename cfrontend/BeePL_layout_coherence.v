(* Writable cells must agree exactly at an alias, or occupy disjoint bytes.
   In particular, equal physical chunks do not justify distinct nominal types. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_array_proofs.
Require Import BeePL_initializer_frames.
Import ListNotations.
Local Open Scope Z_scope.

Definition coherent_layout (cells : scalar_layout) : Prop :=
  forall b ofs ty chunk, cells b ofs ty chunk -> layout_write_compatible cells b ofs ty chunk.

Lemma coherent_layout_write_compatible : forall cells b ofs ty chunk,
  coherent_layout cells -> cells b ofs ty chunk -> layout_write_compatible cells b ofs ty chunk.
Proof. intros; eauto. Qed.

Lemma empty_layout_coherent : coherent_layout (fun _ _ _ _ => False).
Proof. intros b ofs ty chunk H; contradiction. Qed.

Lemma coherent_layout_subset : forall cells cells',
  coherent_layout cells ->
  (forall b ofs ty chunk, cells' b ofs ty chunk -> cells b ofs ty chunk) ->
  coherent_layout cells'.
Proof. intros cells cells' Hcoherent Hsub b ofs ty chunk Hentry old off t ch Hold.
  eapply Hcoherent; eauto. Qed.

Theorem fresh_primitive_array_layout_coherent : forall cells fresh pt count,
  coherent_layout cells ->
  (forall ofs ty chunk, ~ cells fresh ofs ty chunk) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  coherent_layout (extend_array_layout cells fresh pt count).
Proof.
  intros cells fresh pt count Hcoherent Hfresh Hbound b ofs ty chunk Hentry old off t ch Hold.
  destruct Hentry as [Hentry | [i [Hi [Hb [Hofs [Hty Hchunk]]]]]];
    destruct Hold as [Hold | [j [Hj [Holdb [Hoff [Ht Hch]]]]]].
  - eapply Hcoherent; eauto.
  - subst old off t ch. right; left. intro Heq. subst b. eapply Hfresh; eauto.
  - subst b ofs ty chunk. right; left. intro Heq. subst old. eapply Hfresh; eauto.
  - subst b ofs ty chunk old off t ch.
    pose proof (primitive_size_positive pt) as Hsize.
    apply Nat2Z.inj_lt in Hi. apply Nat2Z.inj_lt in Hj.
    assert (Hrange_i : 0 <= Z.of_nat i * sizeof_ptype pt <= Ptrofs.max_unsigned) by nia.
    assert (Hrange_j : 0 <= Z.of_nat j * sizeof_ptype pt <= Ptrofs.max_unsigned) by nia.
    destruct (Nat.eq_dec i j) as [Heq|Hneq].
    + subst j. left. repeat split; reflexivity.
    + right; right. rewrite !Ptrofs.unsigned_repr by assumption.
      rewrite primitive_chunk_size. destruct (Z_lt_ge_dec (Z.of_nat i) (Z.of_nat j)).
      * left; nia.
      * right. assert (Z.of_nat i <> Z.of_nat j) by (intro Heq; apply Hneq; apply Nat2Z.inj; exact Heq). nia.
Qed.

Theorem allocated_primitive_array_layout_coherent :
  forall cenv Sigma cells m allocated fresh pt count size,
  coherent_layout cells -> typed_memory_layout cenv Sigma cells m ->
  Mem.alloc m 0 size = (allocated, fresh) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  coherent_layout (extend_array_layout cells fresh pt count).
Proof.
  intros cenv Sigma cells m allocated fresh pt count size Hcoherent Hmemory Halloc Hbound.
  apply fresh_primitive_array_layout_coherent; try assumption.
  intros ofs ty chunk Hentry.
  assert (Hvalid : Mem.valid_block m fresh).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies;
      [exact (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hentry))|constructor]. }
  eapply Mem.fresh_block_alloc; eauto.
Qed.

Theorem initialized_primitive_array_layout_coherent :
  forall ge cenv Sigma bookkeeping bookkeeping' cells arr pt len attr vs vm m vm' final fresh,
  coherent_layout cells -> typed_memory_layout cenv Sigma cells m ->
  sem_array_init ge bookkeeping arr (Atype (Vtype pt) len attr) vs vm m vm' final bookkeeping' ->
  PTree.get arr vm' = Some (fresh, Atype (Vtype pt) len attr) ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  coherent_layout (extend_array_layout cells fresh pt (length vs)).
Proof.
  intros ge cenv Sigma bookkeeping bookkeeping' cells arr pt len attr vs vm m vm' final fresh
    Hcoherent Hmemory Hinit Hlookup Hbound.
  destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hinit)
    as [allocated [actual [Halloc [Hget [Hhelper [Hlen [HS Hvm]]]]]]].
  assert (actual = fresh) by congruence. subst actual len.
  eapply allocated_primitive_array_layout_coherent; eauto.
Qed.

Theorem completed_primitive_array_layout_coherent :
  forall ge cenv Sigma cells p vm m arr pt len attr es final vm' fresh,
  coherent_layout cells -> typed_memory_layout cenv Sigma cells m ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  ssem_expr ge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm'
    (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ->
  coherent_layout (extend_array_layout cells fresh pt (length es)).
Proof.
  intros ge cenv Sigma cells p vm m arr pt len attr es final vm' fresh Hcoherent Hmemory Hvalues Hbound Hstep.
  inversion Hstep; subst.
  rewrite <- (extracted_value_arguments_length es Hvalues).
  eapply initialized_primitive_array_layout_coherent; eauto.
Qed.

Print Assumptions fresh_primitive_array_layout_coherent.
Print Assumptions completed_primitive_array_layout_coherent.
