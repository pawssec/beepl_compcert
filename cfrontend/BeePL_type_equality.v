(* Checked soundness of BeePL's structural Boolean type comparisons. *)
Require Import List Bool ZArith AST Ctypes BeeTypes.

Lemma eq_effect_label_sound : forall x y, eq_effect_label x y = true -> x = y.
Proof. destruct x, y; simpl; intros; congruence. Qed.

Lemma eq_effect_sound : forall xs ys, eq_effect xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H; try discriminate; auto.
  apply Bool.andb_true_iff in H as [Hhead Htail].
  apply eq_effect_label_sound in Hhead. apply IH in Htail. congruence.
Qed.

Lemma eq_primitive_type_sound : forall x y, eq_primitive_type x y = true -> x = y.
Proof.
  destruct x, y; simpl; intros H; try discriminate; try reflexivity;
  repeat match goal with
    | H : context [Ctyping.intsize_eq ?a ?b] |- _ => destruct (Ctyping.intsize_eq a b); simpl in H; try discriminate
    | H : context [Ctyping.signedness_eq ?a ?b] |- _ => destruct (Ctyping.signedness_eq a b); simpl in H; try discriminate
    | H : context [attr_eq ?a ?b] |- _ => destruct (attr_eq a b); simpl in H; try discriminate
  end; subst; reflexivity.
Qed.

Lemma eq_basic_type_sound : forall x y, eq_basic_type x y = true -> x = y.
Proof.
  destruct x, y; simpl; intros H; try discriminate;
    repeat match goal with H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?] end.
  - f_equal. apply eq_primitive_type_sound; assumption.
  - match goal with H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H end.
    destruct (attr_eq a a0); simpl in *; try discriminate. subst; reflexivity.
  - match goal with H : eq_primitive_type _ _ = true |- _ => apply eq_primitive_type_sound in H end.
    match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end.
    destruct (attr_eq a a0); simpl in *; try discriminate. subst; reflexivity.
Qed.

Fixpoint eq_type_sound (x : type) : forall y, eq_type x y = true -> x = y
with eq_ptr_type_sound (x : ptr_type) : forall y, eq_ptr_type x y = true -> x = y.
Proof.
  - destruct x; intros y; destruct y; simpl; intros H; try discriminate; try reflexivity;
      repeat match goal with H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?] end.
    + f_equal. eapply eq_primitive_type_sound; eauto.
    + f_equal. eapply eq_ptr_type_sound; eauto.
    + match goal with H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H end.
      destruct (attr_eq a a0); simpl in *; try discriminate. subst; reflexivity.
    + match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end.
      destruct (attr_eq a a0); simpl in *; try discriminate. subst.
      f_equal. eapply eq_type_sound; eauto.
    + assert (Hargs : l = l0).
      { revert l0 H. induction l as [|arg rest IH]; intros other Heq;
          destruct other as [|arg' rest']; simpl in Heq; try discriminate; auto.
        apply Bool.andb_true_iff in Heq as [Hhead Htail].
        f_equal; [eapply eq_type_sound; exact Hhead | apply IH; exact Htail]. }
      apply eq_effect_sound in H2. pose proof (proj1 (Bool.eqb_true_iff b b0) H0) as Hb.
      subst l0 e0 b0. f_equal. eapply eq_type_sound; exact H1.
  - destruct x; intros y; destruct y; simpl; intros H; try discriminate;
      repeat match goal with H : (_ && _) = true |- _ => apply Bool.andb_true_iff in H as [? ?] end.
    + destruct (attr_eq a a0); simpl in *; try discriminate. subst.
      f_equal. eapply eq_basic_type_sound; eauto.
    + f_equal. eapply eq_ptr_type_sound; exact H.
    + assert (Hargs : l = l0).
      { revert l0 H. induction l as [|arg rest IH]; intros other Heq;
          destruct other as [|arg' rest']; simpl in Heq; try discriminate; auto.
        apply Bool.andb_true_iff in Heq as [Hhead Htail].
        f_equal; [eapply eq_type_sound; exact Hhead | apply IH; exact Htail]. }
      apply eq_effect_sound in H2. pose proof (proj1 (Bool.eqb_true_iff b b0) H0) as Hb.
      subst l0 e0 b0. f_equal. eapply eq_type_sound; exact H1.
Defined.

Lemma eq_types_sound : forall xs ys, eq_types eq_type xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H; try discriminate; auto.
  apply Bool.andb_true_iff in H as [Hhead Htail].
  f_equal; [apply eq_type_sound; exact Hhead | apply IH; exact Htail].
Qed.

Print Assumptions eq_type_sound.
Print Assumptions eq_ptr_type_sound.
Print Assumptions eq_types_sound.

