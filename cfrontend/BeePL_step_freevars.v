(* Typed source transitions cannot introduce new caller-visible free names. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_substitution_freevars.
Require Import BeePL_typed_substitution_freevars BeePL_match_arity BeePL_packet_match_freevars.
Import ListNotations.

Lemma incl_empty_names : forall names : list ident, incl [] names.
Proof. intros names x H; contradiction. Qed.

Theorem typed_step_free_variables_mutual : forall ge,
  (forall p vm m es final vm' es', ssem_exprs ge p vm m es final vm' es' ->
    forall Gamma Sigma ef ts, type_exprs ge.(genv_cenv) Gamma Sigma es ef ts ->
    incl (expression_list_variables es') (expression_list_variables es)) /\
  (forall p vm m e final vm' e', ssem_expr ge p vm m e final vm' e' ->
    forall Gamma Sigma ef ty, type_expr ge.(genv_cenv) Gamma Sigma e ef ty ->
    incl (free_variables e') (free_variables e)).
Proof.
  intros ge. apply ssem_exprs_ssem_expr_ind_mut;
    intros; match goal with Htyped : type_expr _ _ _ _ _ _ |- _ => inversion Htyped; subst
      | Htyped : type_exprs _ _ _ _ _ _ |- _ => inversion Htyped; subst end;
    cbn [free_variables expression_list_variables List.map List.concat seq.map seq.flatten seq.foldr] in *;
    try solve [apply incl_empty_names];
    try solve [apply incl_refl];
    try solve [eauto using incl_app_pair, incl_remove, incl_refl, incl_appl, incl_appr, incl_app].
  - apply (proj1 (substitution_relation_function _ _)) in s. subst e2'.
    eapply typed_value_substitution_removes_variable; exact H11.
  - destruct (Z.to_nat n); cbn [free_variables seq.cat];
      eauto using incl_empty_names, incl_app, incl_refl.
  - inversion H4; subst. simpl in H8. destruct H8 as [bound [Horder|Horder]];
      inversion Horder; subst; cbn [eq_pattern match_branch_variables remove_pattern_variables vars_bound_by seq.cat];
      eauto using incl_appl, incl_appr, incl_refl.
  - cbn [seq.cat match_branch_variables remove_pattern_variables vars_bound_by].
    eapply incl_tran; [eapply typed_value_substitution_removes_variable|].
    + match goal with Hbranch : forall n pat branch, nth_error _ n = Some pat -> nth_error _ n = Some branch -> _ |- _ =>
        eapply (Hbranch 1%nat (Psome x) esome); reflexivity end.
    + apply incl_appr. apply incl_appl; apply incl_refl.
  - cbn [seq.cat match_branch_variables remove_pattern_variables vars_bound_by].
    eapply incl_tran; [eapply typed_value_substitution_removes_variable|].
    + match goal with Hbranch : forall n pat branch, nth_error _ n = Some pat -> nth_error _ n = Some branch -> _ |- _ =>
        eapply (Hbranch O (Psome x) esome); reflexivity end.
    + apply incl_appl; apply incl_refl.
  - cbn [seq.cat match_branch_variables].
    eapply incl_tran; [eapply execute_packet_match_freevars|].
    + eapply typed_match_arity.
      match goal with Hbranch : forall n pat branch, nth_error _ n = Some pat -> nth_error _ n = Some branch -> _ |- _ =>
        eapply (Hbranch O _ yes); reflexivity end.
    + eapply typed_match_arity.
      match goal with Hbranch : forall n pat branch, nth_error _ n = Some pat -> nth_error _ n = Some branch -> _ |- _ =>
        eapply (Hbranch 1%nat _ no); reflexivity end.
    + eassumption.
    + rewrite app_nil_r. apply incl_refl.
  - match goal with Hargs : type_exprs _ _ _ (_ :: _) _ _ |- _ => inversion Hargs; subst end.
    apply incl_app_pair; [eauto|apply incl_refl].
  - match goal with Hargs : type_exprs _ _ _ (_ :: _) _ _ |- _ => inversion Hargs; subst end.
    cbn [seq.cat]. eauto.
Qed.

Theorem typed_step_free_variables : forall ge p vm m e final vm' next Gamma Sigma ef ty,
  ssem_expr ge p vm m e final vm' next ->
  type_expr ge.(genv_cenv) Gamma Sigma e ef ty ->
  incl (free_variables next) (free_variables e).
Proof. intros; eapply (proj2 (typed_step_free_variables_mutual ge)); eauto. Qed.

Print Assumptions typed_step_free_variables.
