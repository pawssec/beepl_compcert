(* Free-variable facts needed by value-substitution typing. *)
Require Import ZArith List AST BeeTypes BeePL BeePL_values.

Definition expression_list_variables (es : list expr) : list ident :=
  List.concat (List.map free_variables es).

Lemma substituted_list_variables : forall x v t es,
  (forall e, In e es -> incl (free_variables (subst x (Val v t) e)) (free_variables e)) ->
  incl (expression_list_variables (substs subst x (Val v t) es))
       (expression_list_variables es).
Proof.
  intros x v t es. induction es as [|e es IH]; intros Hall z Hz.
  - inversion Hz.
  - change (In z (free_variables (subst x (Val v t) e) ++
      expression_list_variables (substs subst x (Val v t) es))) in Hz.
    change (In z (free_variables e ++ expression_list_variables es)).
    apply in_app_iff in Hz. apply in_app_iff. destruct Hz as [Hz | Hz].
    + left. apply (Hall e (or_introl eq_refl)); exact Hz.
    + right. apply IH; [|exact Hz].
      intros e' Hin. apply Hall. right; exact Hin.
Qed.

Lemma substituted_branch_variables : forall x v t es ps,
  (forall e, In e es -> incl (free_variables (subst x (Val v t) e)) (free_variables e)) ->
  incl (expression_list_variables (subst_match_branches subst x (Val v t) ps es))
       (expression_list_variables es).
Proof.
  intros x v t es. induction es as [|e es IH]; intros ps Hall z Hz.
  - inversion Hz.
  - destruct ps as [|pat ps]; [exact Hz |].
    cbn [subst_match_branches] in Hz.
    destruct (x_in_pattern x pat) eqn:Hbound;
      change (In z (free_variables e ++ expression_list_variables es));
      apply in_app_iff;
      cbn [expression_list_variables List.map List.concat] in Hz;
      apply in_app_iff in Hz; destruct Hz as [Hz | Hz].
    + left; exact Hz.
    + right. eapply IH; [|exact Hz]. intros e' Hin. apply Hall. right; exact Hin.
    + left. apply (Hall e (or_introl eq_refl)); exact Hz.
    + right. eapply IH; [|exact Hz]. intros e' Hin. apply Hall. right; exact Hin.
Qed.

Lemma incl_app_pair : forall (A : Type) (xs xs' ys ys' : list A),
  incl xs xs' -> incl ys ys' -> incl (xs ++ ys) (xs' ++ ys').
Proof.
  intros A xs xs' ys ys' Hx Hy z Hz.
  apply in_app_iff in Hz. apply in_app_iff. destruct Hz; auto.
Qed.

Lemma incl_remove : forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b}) x xs ys,
  incl xs ys -> incl (remove dec x xs) (remove dec x ys).
Proof.
  intros A dec x xs ys H z Hz. apply in_remove in Hz as [Hin Hneq].
  apply in_in_remove; [congruence | apply H; exact Hin].
Qed.

Lemma remove_pattern_variables_incl : forall pat xs ys,
  incl xs ys -> incl (remove_pattern_variables pat xs) (remove_pattern_variables pat ys).
Proof.
  intros pat xs ys H. unfold remove_pattern_variables.
  induction (vars_bound_by pat) as [|x rest IH]; simpl; auto using incl_remove.
Qed.

Lemma substituted_scoped_branch_variables : forall x v t es ps,
  (forall e, In e es -> incl (free_variables (subst x (Val v t) e)) (free_variables e)) ->
  incl (match_branch_variables ps (List.map free_variables (subst_match_branches subst x (Val v t) ps es)))
       (match_branch_variables ps (List.map free_variables es)).
Proof.
  intros x v t es. induction es as [|e rest IH]; intros ps Hall.
  - simpl; apply incl_refl.
  - destruct ps as [|pat pats]; [simpl; apply incl_refl|].
    cbn [subst_match_branches]. destruct (x_in_pattern x pat);
      cbn [List.map match_branch_variables]; apply incl_app_pair.
    + apply incl_refl.
    + apply IH. intros child Hin; apply Hall; right; exact Hin.
    + apply remove_pattern_variables_incl. apply Hall; left; reflexivity.
    + apply IH. intros child Hin; apply Hall; right; exact Hin.
Qed.

Lemma value_substitution_free_variables : forall x v t e,
  incl (free_variables (subst x (Val v t) e)) (free_variables e).
Proof.
  intros x v t. apply expr_ind_rec; intros; cbn [subst free_variables];
    try solve [apply incl_refl];
    try solve [eauto using incl_app_pair, substituted_list_variables, substituted_branch_variables, substituted_scoped_branch_variables].
  - destruct (Pos.eqb x x0); cbn [free_variables]; [intros z Hz; inversion Hz | apply incl_refl].
  - destruct (Pos.eqb x x0); cbn [free_variables];
      apply incl_app_pair; auto using incl_remove, incl_refl.
  - destruct (Pos.eqb x a); cbn [free_variables];
      [intros z Hz; inversion Hz | apply incl_refl].
Qed.

Print Assumptions value_substitution_free_variables.

Lemma in_vars_spec : forall x xs, in_vars x xs = true <-> In x xs.
Proof.
  intros x xs. induction xs as [|a xs IH]; simpl.
  - split; [discriminate | contradiction].
  - destruct (ident_eq x a) as [Heq | Hneq].
    + subst. split; auto.
    + rewrite IH. intuition congruence.
Qed.

Lemma disjoint_vars_spec : forall xs ys,
  disjoint_vars xs ys = true <-> forall x, In x xs -> ~ In x ys.
Proof.
  intros xs. induction xs as [|a xs IH]; intros ys; simpl.
  - split; [intros _ x H; contradiction | intros; reflexivity].
  - destruct (in_vars a ys) eqn:Ha.
    + split; [discriminate |]. intros H. exfalso.
      apply (H a (or_introl eq_refl)). apply in_vars_spec. exact Ha.
    + rewrite IH. split.
      * intros H x [Heq | Hin].
        -- subst. intro Hin. apply in_vars_spec in Hin. congruence.
        -- apply H. exact Hin.
      * intros H x Hin. apply H. right; exact Hin.
Qed.

Lemma disjoint_vars_incl : forall xs ys xs' ys',
  incl xs' xs -> incl ys' ys -> disjoint_vars xs ys = true ->
  disjoint_vars xs' ys' = true.
Proof.
  intros xs ys xs' ys' Hx Hy Hd. pose proof (proj1 (disjoint_vars_spec xs ys) Hd) as Hdisjoint.
  apply disjoint_vars_spec. intros x Hxin Hyin.
  apply (Hdisjoint x (Hx x Hxin)). apply Hy. exact Hyin.
Qed.

Lemma value_substitution_disjoint : forall x v t e1 e2,
  disjoint_vars (free_variables e1) (free_variables e2) = true ->
  disjoint_vars (free_variables (subst x (Val v t) e1))
                (free_variables (subst x (Val v t) e2)) = true.
Proof.
  intros. eapply disjoint_vars_incl; eauto using value_substitution_free_variables.
Qed.

Print Assumptions value_substitution_disjoint.

(* A suspended callee is closed relative to the caller; its own environment
   resolves body variables independently of the caller's substitutions. *)
Lemma callframe_caller_free_variables : forall callee_vm body ty,
  free_variables (CallFrame callee_vm body ty) = nil.
Proof. reflexivity. Qed.
