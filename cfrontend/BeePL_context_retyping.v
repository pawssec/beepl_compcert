(* Transfer effect choices between derivations of the same annotated syntax.
   This is not effect uniqueness: match branches may choose larger effects. *)
Require Import List AST Maps BeeTypes BeePL BeePL_typesystem.
Require Import BeePL_substitution_proofs.

Theorem typing_context_retyping :
  (forall cenv Gamma Sigma es ef ts,
    type_exprs cenv Gamma Sigma es ef ts ->
    forall Gamma' ef' ts', type_exprs cenv Gamma' Sigma es ef' ts' ->
    type_exprs cenv Gamma' Sigma es ef ts) /\
  (forall cenv Gamma Sigma e ef ty,
    type_expr cenv Gamma Sigma e ef ty ->
    forall Gamma' ef' ty', type_expr cenv Gamma' Sigma e ef' ty' ->
    type_expr cenv Gamma' Sigma e ef ty).
Proof.
  apply type_exprs_type_expr_ind_mut; intros;
    match goal with
    | Hsecond : type_exprs ?c ?G ?S ?es _ _ |- type_exprs ?c ?G ?S ?es _ _ => inversion Hsecond; subst
    | Hsecond : type_expr ?c ?G ?S ?e _ _ |- type_expr ?c ?G ?S ?e _ _ => inversion Hsecond; subst
    end;
    try solve [econstructor; eauto 5].
  all: repeat match goal with
    | Hleft : type_expr ?c ?G1 ?S ?e ?ef1 ?t1,
      Hright : type_expr ?c ?G2 ?S ?e ?ef2 ?t2 |- _ =>
        let Heq := fresh "Hannotation" in
        assert (Heq : t1 = t2) by
          (rewrite <- (type_rel_typeof _ _ _ _ _ _ Hleft);
           exact (type_rel_typeof _ _ _ _ _ _ Hright));
        first [progress subst | progress (injection Heq; intros; subst)]
    end.
  all: try solve [econstructor; eauto 5].
  - eapply ty_cond with (ef2 := ef2) (ef3 := ef3) (branch_effect := branch_effect); eauto.
  - eapply ty_sinit with (co := co) (bts := bts); eauto.
  - eapply ty_matcho with (te := te0) (branch_effect := branch_effect); eauto.
  - eapply ty_ainit with (aty := aty) (ts := ts); eauto.
  - eapply ty_loopframe with (active_effect := active_effect); [eauto | eauto | assumption].
Qed.

Corollary expression_context_retyping :
  forall cenv Gamma Sigma e ef ty Gamma' ef' ty',
  type_expr cenv Gamma Sigma e ef ty ->
  type_expr cenv Gamma' Sigma e ef' ty' ->
  type_expr cenv Gamma' Sigma e ef ty.
Proof. intros; eapply (proj2 typing_context_retyping); eauto. Qed.

Corollary expressions_context_retyping :
  forall cenv Gamma Sigma es ef ts Gamma' ef' ts',
  type_exprs cenv Gamma Sigma es ef ts ->
  type_exprs cenv Gamma' Sigma es ef' ts' ->
  type_exprs cenv Gamma' Sigma es ef ts.
Proof. intros; eapply (proj1 typing_context_retyping); eauto. Qed.

Print Assumptions typing_context_retyping.
Print Assumptions expression_context_retyping.

