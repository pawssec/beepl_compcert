(* Source expressions contain no captured runtime call environments. *)
Require Import List ZArith Integers AST Maps Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typechecker BeePL_substitution_proofs.
Require Import BeePL_runtime_locations.
Import ListNotations.

Fixpoint frame_free (e : expr) : Prop :=
  match e with
  | CallFrame _ _ _ | LoopFrame _ _ _ => False
  | App f es _ => frame_free f /\ all_expr_locations frame_free es
  | Prim _ es _ | Sinit _ _ es _ | Ebytes es _ | Ainit _ _ es _ => all_expr_locations frame_free es
  | Bind _ _ e1 e2 _ => frame_free e1 /\ frame_free e2
  | Cond e1 e2 e3 _ | For e1 e2 _ e3 _ => frame_free e1 /\ frame_free e2 /\ frame_free e3
  | Sfield e _ _ | Esome e _ => frame_free e
  | Match e _ es _ => frame_free e /\ all_expr_locations frame_free es
  | _ => True
  end.

Lemma substs_frame_free : forall x v t es,
  all_expr_locations (frame_free) es ->
  (forall e, In e es -> frame_free e -> frame_free (subst x (Val v t) e)) ->
  all_expr_locations (frame_free) (substs subst x (Val v t) es).
Proof.
  intros x v t es. induction es as [|e es IH]; intros Hall Hstep; simpl; constructor.
  - apply Hstep; [left; reflexivity | destruct Hall; assumption].
  - apply IH; [destruct Hall; assumption |]. intros e' Hin. apply Hstep. right; exact Hin.
Qed.


Lemma match_substs_frame_free : forall x v t es ps,
  all_expr_locations (frame_free) es ->
  (forall e, In e es -> frame_free e -> frame_free (subst x (Val v t) e)) ->
  all_expr_locations (frame_free) (subst_match_branches subst x (Val v t) ps es).
Proof.
  intros x v t es. induction es as [|e es IH]; intros ps Hall Hstep; simpl; [constructor |].
  destruct ps as [|pat ps]; [exact Hall |]. simpl.
  destruct Hall as [Hhead Htail]. destruct (x_in_pattern x pat); constructor; auto.
  - apply IH; auto. intros e' Hin. apply Hstep. right; exact Hin.
  - apply Hstep; auto. left; reflexivity.
  - apply IH; auto. intros e' Hin. apply Hstep. right; exact Hin.
Qed.

Lemma value_substitution_frame_free : forall x v t,
  forall e,
  frame_free e -> frame_free (subst x (Val v t) e).
Proof.
  intros x v t e. induction e using expr_ind_rec; intros; cbn [subst frame_free] in *;
    try solve [intuition eauto using substs_frame_free, match_substs_frame_free].
  - destruct (Pos.eqb x x0); simpl; auto.
  - destruct (Pos.eqb x x0); simpl; intuition.
  - destruct (Pos.eqb x a); simpl; auto.
Qed.


Lemma frame_free_value_substitution_relation : forall x v t e e',
  frame_free e -> SubstE x (Val v t) e e' -> frame_free e'.
Proof.
  intros x v t e e' Hfree Hsubst.
  apply substitution_relation_iff in Hsubst. subst e'.
  apply value_substitution_frame_free; exact Hfree.
Qed.

Lemma frame_free_match_value_substitution : forall x v t ps es,
  all_expr_locations frame_free es ->
  all_expr_locations frame_free (subst_match_branches subst x (Val v t) ps es).
Proof.
  intros. eapply match_substs_frame_free; eauto using value_substitution_frame_free.
Qed.

Lemma checked_list_members : forall cenv Gamma Sigma es ts ef,
  type_check_exprs type_check_expr cenv Gamma Sigma es = OK (ts, ef) ->
  forall e, In e es -> exists t effects, type_check_expr cenv Gamma Sigma e = OK (t, effects).
Proof.
  intros cenv Gamma Sigma es. induction es as [|e es IH]; intros ts ef Hcheck member Hin.
  - contradiction.
  - simpl in Hcheck.
    destruct (type_check_expr cenv Gamma Sigma e) as [[t effects]|err] eqn:Hhead; try discriminate.
    destruct (type_check_exprs type_check_expr cenv Gamma Sigma es) as [[types efs]|err] eqn:Htail;
      try discriminate.
    destruct Hin as [Heq|Hin].
    + subst member. eauto.
    + eapply IH; eauto.
Qed.

Print Assumptions value_substitution_frame_free.
Print Assumptions frame_free_match_value_substitution.

Theorem type_checker_success_frame_free : forall e cenv Gamma Sigma t ef,
  type_check_expr cenv Gamma Sigma e = OK (t, ef) -> frame_free e.
Proof.
  induction e using expr_ind_rec; intros cenv Gamma Sigma result effects Hcheck;
    cbn [type_check_expr Errors.bind2 Errors.bind] in Hcheck; cbn [frame_free].
  all: repeat match type of Hcheck with
  | context [Errors.bind2 ?chk ?cont] => destruct chk eqn:?; cbn [Errors.bind2] in Hcheck; try discriminate
  | context [Errors.bind ?chk ?cont] => destruct chk eqn:?; cbn [Errors.bind] in Hcheck; try discriminate
  | context [match ?scrut with _ => _ end] =>
      destruct scrut eqn:?; cbn [Errors.bind2 Errors.bind] in Hcheck; try discriminate
  end.
  all: try discriminate.
  all: repeat split.
  all: try solve [eauto].
  all: try (apply all_expr_locations_Forall; apply Forall_forall; intros member Hin).
  all: try match goal with
  | Hlist : type_check_exprs type_check_expr _ _ _ ?es = OK (_, _) , Hin : In ?member ?es |- _ =>
      destruct (checked_list_members _ _ _ _ _ _ Hlist member Hin) as [ty [efs Hchecked]]
  end.
  all: repeat match goal with
  | Hin : In _ (_ :: _) |- _ => destruct Hin as [Heq|Hin]; [subst|]
  end.
  all: try contradiction.
  all: try solve [eauto 8].
  all: match goal with
  | IH : forall e, In e ?es -> forall c G S t ef, _ -> frame_free e,
    HC : type_check_expr ?c ?G ?S ?e = OK (?ty, ?ef) |- frame_free ?e =>
      eapply (IH e); [simpl; auto|exact HC]
  end.
Qed.
Print Assumptions type_checker_success_frame_free.

Corollary checked_function_body_frame_free : forall cenv Gamma Sigma fn success,
  type_check_function cenv Gamma Sigma fn = OK success -> frame_free fn.(fn_body).
Proof.
  intros cenv Gamma Sigma fn success Hcheck. unfold type_check_function in Hcheck.
  destruct (type_check_expr cenv (bind_vars Gamma fn.(fn_args)) Sigma fn.(fn_body))
    as [[ty ef]|error] eqn:Hbody.
  - eapply type_checker_success_frame_free; exact Hbody.
  - repeat match type of Hcheck with
    | context [if ?guard then _ else _] => destruct guard; try discriminate
    end.
Qed.
Print Assumptions checked_function_body_frame_free.
