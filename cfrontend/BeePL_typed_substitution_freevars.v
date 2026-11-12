(* Typed Match branches have matching pattern arity. This is essential:
   malformed unmatched branches intentionally retain their old substitution
   behavior, so binder removal is not claimed for arbitrary syntax. *)
Require Import List ZArith Bool AST Maps.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_substitution_freevars.
Import ListNotations.

Lemma in_remove_pattern_variables : forall pat vars x,
  In x (remove_pattern_variables pat vars) <-> In x vars /\ ~ In x (vars_bound_by pat).
Proof.
  intros pat vars x. unfold remove_pattern_variables.
  induction (vars_bound_by pat) as [|a rest IH]; simpl.
  - tauto.
  - split.
    + intros H. apply in_remove in H as [H Hneq]. apply IH in H. intuition congruence.
    + intros [Hin Hnot]. apply in_in_remove; [intuition congruence|]. apply IH. tauto.
Qed.

Lemma x_in_xs_spec : forall x xs, x_in_xs x xs = true <-> In x xs.
Proof.
  intros x xs; induction xs as [|a rest IH]; simpl; [split; [discriminate|contradiction]|].
  destruct (Pos.eqb x a) eqn:Heq.
  - apply Pos.eqb_eq in Heq; subst; tauto.
  - apply Pos.eqb_neq in Heq. rewrite IH; intuition congruence.
Qed.

Lemma substituted_scoped_branches_notin : forall x v t ps es,
  length ps = length es ->
  (forall n pat branch, nth_error ps n = Some pat -> nth_error es n = Some branch ->
    ~ In x (free_variables (subst x (Val v t) branch))) ->
  ~ In x (match_branch_variables ps
    (List.map free_variables (subst_match_branches subst x (Val v t) ps es))).
Proof.
  intros x v t ps; induction ps as [|pat pats IH]; intros es Hlen Hall;
    destruct es as [|e rest]; simpl in Hlen; try discriminate; [simpl; tauto|].
  cbn [subst_match_branches]. destruct (x_in_pattern x pat) eqn:Hbound;
    cbn [List.map match_branch_variables]; rewrite in_app_iff; intros [Hhead|Htail].
  - apply in_remove_pattern_variables in Hhead as [_ Hnot]. apply Hnot.
    apply x_in_xs_spec. exact Hbound.
  - eapply (IH rest); [inversion Hlen; reflexivity| |exact Htail].
    intros n p b Hp Hb; eapply (Hall (S n)); eauto.
  - apply in_remove_pattern_variables in Hhead as [Hin _].
    eapply (Hall O pat e); [reflexivity|reflexivity|exact Hin].
  - eapply (IH rest); [inversion Hlen; reflexivity| |exact Htail].
    intros n p b Hp Hb; eapply (Hall (S n)); eauto.
Qed.

Lemma typed_value_substitution_notin :
  (forall env Gamma Sigma es ef ts, type_exprs env Gamma Sigma es ef ts ->
    forall x v ty, ~ In x (expression_list_variables (substs subst x (Val v ty) es))) /\
  (forall env Gamma Sigma e ef t, type_expr env Gamma Sigma e ef t ->
    forall x v ty, ~ In x (free_variables (subst x (Val v ty) e))).
Proof.
  apply type_exprs_type_expr_ind_mut;
    intros; cbn [subst free_variables substs expression_list_variables List.map List.concat seq.map seq.flatten seq.foldr seq.cat] in *;
    try solve [intuition];
    try solve [repeat rewrite in_app_iff; intuition eauto].
  - destruct (Pos.eqb x0 x) eqn:Heq; simpl; [tauto|].
    apply Pos.eqb_neq in Heq. intuition congruence.
  - destruct (Pos.eqb x0 x) eqn:Heq; cbn [free_variables]; rewrite in_app_iff; intros [Hin|Hin].
    + eapply H; exact Hin.
    + apply Pos.eqb_eq in Heq; subst x0. apply in_remove in Hin; intuition.
    + eapply H; exact Hin.
    + apply in_remove in Hin as [Hin _]. eapply H0; exact Hin.
  - rewrite in_app_iff. intros [Hin|Hin].
    + exact (H x v0 ty Hin).
    + eapply (substituted_scoped_branches_notin x v0 ty ps es); [exact e0| |exact Hin].
      intros n pat branch Hp Hb. exact (H0 n pat branch Hp Hb x v0 ty).
  - destruct (Pos.eqb x a) eqn:Heq; simpl; [tauto|].
    apply Pos.eqb_neq in Heq. intuition congruence.
Qed.

Theorem typed_value_substitution_removes_variable : forall env Gamma Sigma e ef t x v ty,
  type_expr env Gamma Sigma e ef t ->
  incl (free_variables (subst x (Val v ty) e)) (remove ident_eq x (free_variables e)).
Proof.
  intros * Htyped y Hin. apply in_in_remove.
  - intro Heq; subst y. eapply (proj2 typed_value_substitution_notin); eauto.
  - eapply value_substitution_free_variables; exact Hin.
Qed.

Print Assumptions typed_value_substitution_removes_variable.
