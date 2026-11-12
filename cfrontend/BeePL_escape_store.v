(* Actual scalar writes cannot introduce pointer fragments. No compiler or
   lifetime-simulation assumption is used. Aggregate padding is not covered. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Memdata Values Integers Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_soundness_store.
Import ListNotations.
Local Open Scope Z_scope.

Definition pointer_fragment (mv : memval) : Prop :=
  exists b ofs q n, mv = Fragment (Vptr b ofs) q n.
Definition no_pointer_fragments (bytes : list memval) : Prop :=
  Forall (fun mv => ~ pointer_fragment mv) bytes.
Definition pointer_fragments_preserved (before after : mem) : Prop :=
  forall b ofs target delta q n,
    ZMap.get ofs (PMap.get b (Mem.mem_contents after)) =
      Fragment (Vptr target delta) q n ->
    ZMap.get ofs (PMap.get b (Mem.mem_contents before)) =
      Fragment (Vptr target delta) q n.

Lemma bytes_have_no_pointer_fragments : forall bytes,
  no_pointer_fragments (inj_bytes bytes).
Proof.
  induction bytes; simpl; constructor; auto.
  intros [b [ofs [q [n H]]]]; discriminate.
Qed.
Lemma repeated_undef_has_no_pointer_fragments : forall n,
  no_pointer_fragments (repeat Undef n).
Proof.
  induction n; simpl; constructor; auto.
  intros [b [ofs [q [i H]]]]; discriminate.
Qed.
Lemma nonpointer_fragments : forall v,
  (forall b ofs, v <> Vptr b ofs) -> forall n q,
  no_pointer_fragments (inj_value_rec n v q).
Proof.
  intros v H n; induction n; intros q; simpl; constructor; auto.
  intros [b [ofs [q' [i E]]]]. injection E as Ev Eq En. eapply H; exact Ev.
  apply IHn.
Qed.
Lemma nonpointer_encoding : forall chunk v,
  (forall b ofs, v <> Vptr b ofs) ->
  no_pointer_fragments (encode_val chunk v).
Proof.
  intros chunk v H; destruct v; try (exfalso; eapply H; reflexivity);
  destruct chunk; cbn [encode_val]; try apply bytes_have_no_pointer_fragments;
  try apply repeated_undef_has_no_pointer_fragments;
  unfold inj_value; apply nonpointer_fragments; intros; discriminate.
Qed.

Lemma store_bytes_no_new_pointer_fragments : forall m b ofs bytes m',
  Mem.storebytes m b ofs bytes = Some m' ->
  no_pointer_fragments bytes -> pointer_fragments_preserved m m'.
Proof.
  intros m b ofs bytes m' Hstore Hbytes loc pos target delta q n Hget.
  erewrite Mem.storebytes_mem_contents in Hget by exact Hstore.
  destruct (peq loc b) as [E|E].
  - subst loc. rewrite PMap.gss in Hget.
    destruct (zle ofs pos); destruct (zlt pos (ofs + Z.of_nat(length bytes))).
    + pose proof (Mem.setN_in bytes ofs pos (PMap.get b (Mem.mem_contents m)) ltac:(lia)) as Hin.
      rewrite Hget in Hin. apply Forall_forall with (x:=Fragment(Vptr target delta) q n) in Hbytes; auto.
      exfalso; apply Hbytes. exists target,delta,q,n; reflexivity.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
  - rewrite PMap.gso in Hget by congruence. exact Hget.
Qed.

Lemma scalar_store_no_new_pointer_fragments : forall m chunk b ofs v m',
  Mem.store chunk m b ofs v = Some m' ->
  (forall target delta, v <> Vptr target delta) ->
  pointer_fragments_preserved m m'.
Proof.
  intros m chunk b ofs v m' Hstore Hvalue loc pos target delta q n Hget.
  pose proof (nonpointer_encoding chunk v Hvalue) as Hbytes.
  erewrite Mem.store_mem_contents in Hget by exact Hstore.
  destruct (peq loc b) as [E|E].
  - subst loc. rewrite PMap.gss in Hget.
    destruct (zle ofs pos);
      destruct (zlt pos (ofs + Z.of_nat(length (encode_val chunk v)))).
    + pose proof (Mem.setN_in (encode_val chunk v) ofs pos
        (PMap.get b (Mem.mem_contents m)) ltac:(lia)) as Hin.
      rewrite Hget in Hin.
      apply Forall_forall with (x:=Fragment(Vptr target delta) q n) in Hbytes; auto.
      exfalso; apply Hbytes. exists target,delta,q,n; reflexivity.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
    + rewrite Mem.setN_outside in Hget by lia. exact Hget.
  - rewrite PMap.gso in Hget by congruence. exact Hget.
Qed.

Lemma primitive_conversion_not_pointer : forall pt v cv,
  typeof_value v (Vtype pt) -> trans_cvalue_bvalue cv = OK v ->
  forall b ofs, cv <> Vptr b ofs.
Proof.
  intros pt v cv Hshape Hconvert b ofs E; subst cv.
  simpl in Hconvert. inversion Hconvert; subst.
  destruct pt; contradiction.
Qed.

Theorem primitive_assignment_no_new_pointer_fragments :
  forall ge pt m b ofs v m' result,
  typeof_value v (Vtype pt) ->
  assign_addr ge (Vtype pt) m b ofs Full v m' result ->
  pointer_fragments_preserved m m'.
Proof.
  intros ge pt m b ofs v m' result Hshape Hassign.
  inversion Hassign; subst; simpl in *.
  - eapply scalar_store_no_new_pointer_fragments.
    + eassumption.
    + eapply primitive_conversion_not_pointer; eauto.
  - eapply scalar_store_no_new_pointer_fragments.
    + eassumption.
    + intros target delta; destruct b0; discriminate.
  - destruct pt; discriminate.
  - discriminate.
  - discriminate.
Qed.

Theorem typed_primitive_assignment_no_new_pointer_fragments :
  forall ge cenv Gamma Sigma pt m b ofs v m' result,
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
  assign_addr ge (Vtype pt) m b ofs Full v m' result ->
  pointer_fragments_preserved m m'.
Proof.
  intros; eapply primitive_assignment_no_new_pointer_fragments; eauto.
  eapply declarative_value_shape; eauto.
Qed.

Print Assumptions store_bytes_no_new_pointer_fragments.
Print Assumptions typed_primitive_assignment_no_new_pointer_fragments.
