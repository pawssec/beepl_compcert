(* Local checker consistency for branch effect budgets and primitive casts. *)
Require Import List Bool ZArith Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker BeePL_type_equality BeePL_auxlemmas.
Import ListNotations.

Lemma checker_allowed_cast_target : forall source target result,
  allowed_cast source target = OK result -> result = target.
Proof. intros source target result; destruct source; destruct target; simpl; intro H; inversion H; reflexivity. Qed.

Theorem checked_cast_typing : forall env Gamma Sigma e target annotation result effects,
  (forall ty ef, type_check_expr env Gamma Sigma e = OK (ty, ef) -> type_expr env Gamma Sigma e ef ty) ->
  type_check_expr env Gamma Sigma (Prim (Cast target) [e] annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Prim (Cast target) [e] annotation) effects result.
Proof.
  intros env Gamma Sigma e target annotation result effects Hchild Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct target as [|target|pt|sid attr|elem len attr|params eff rt va|]; try discriminate.
  destruct (type_check_expr env Gamma Sigma e) as [[sourceType ef]|err] eqn:Hchildcheck; cbn in Hcheck; try discriminate.
  destruct sourceType as [|source|pt|sid attr|elem len attr|params eff rt va|]; try discriminate.
  destruct (allowed_cast source target) as [output|err] eqn:Hcast; cbn in Hcheck; try discriminate.
  pose proof (checker_allowed_cast_target _ _ _ Hcast); subst output.
  destruct (eq_type annotation (Vtype target)) eqn:Hannotation; try discriminate.
  apply eq_type_sound in Hannotation; subst annotation.
  inversion Hcheck; subst. eapply ty_cast; eauto.
Qed.

Lemma checker_bool_type : forall ty, is_primbool ty = true -> ty = Vtype Tbool.
Proof. intros ty; destruct ty; try discriminate; destruct p; simpl; intro H; try discriminate; reflexivity. Qed.

Theorem checked_conditional_typing : forall env Gamma Sigma guard yes no annotation result effects,
  (forall e, In e [guard; yes; no] -> forall ty ef,
    type_check_expr env Gamma Sigma e = OK (ty, ef) -> type_expr env Gamma Sigma e ef ty) ->
  type_check_expr env Gamma Sigma (Cond guard yes no annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Cond guard yes no annotation) effects result.
Proof.
  intros env Gamma Sigma guard yes no annotation result effects Hchildren Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_expr env Gamma Sigma guard) as [[tg eg]|err] eqn:Hg; cbn in Hcheck; try discriminate.
  destruct (type_check_expr env Gamma Sigma yes) as [[ty ey]|err] eqn:Hy; cbn in Hcheck; try discriminate.
  destruct (type_check_expr env Gamma Sigma no) as [[tn en]|err] eqn:Hn; cbn in Hcheck; try discriminate.
  destruct (is_primbool tg && eq_type ty tn && eq_type annotation ty) eqn:Hguard; try discriminate.
  apply andb_true_iff in Hguard as [Hfirst Hannotation].
  apply andb_true_iff in Hfirst as [Hbool Hbranches].
  apply checker_bool_type in Hbool. apply eq_type_sound in Hbranches. apply eq_type_sound in Hannotation. subst.
  inversion Hcheck; subst.
  eapply ty_cond with (ef2 := ey) (ef3 := en) (branch_effect := ey ++ en).
  - eapply Hchildren; [simpl; auto|exact Hg].
  - eapply Hchildren; [simpl; auto|exact Hy].
  - eapply Hchildren; [simpl; auto|exact Hn].
  - replace ey with (ey ++ []) at 1 by apply app_nil_r.
    apply sub_effect_concat; [apply sub_effect_refl|apply sub_effect_nil].
  - apply sub_effect_1c; apply sub_effect_refl.
Qed.

Definition branch_cast_rejected (r : res (type * effect)) := match r with Error _ => True | OK _ => False end.
Definition branch_cast_int := Vtype (Tint I32 Signed noattr).
Definition branch_cast_ref := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr).
Definition branch_cast_store := PTree.set 1%positive branch_cast_ref empty_stcontext.
Definition branch_cast_check := type_check_expr (PTree.empty _) empty_context branch_cast_store.
Definition branch_cast_pointer := Val (Vloc 1%positive Ptrofs.zero) branch_cast_ref.
Definition branch_cast_zero := Const (ConsInt Int.zero) branch_cast_int.
Example integer_to_bool_cast_accepted :
  branch_cast_check (Prim (Cast (Vtype Tbool)) [branch_cast_zero] (Vtype Tbool)) = OK (Vtype Tbool, []).
Proof. vm_compute; reflexivity. Qed.
Example bool_to_integer_cast_accepted :
  branch_cast_check (Prim (Cast branch_cast_int) [Const (ConsBool true) (Vtype Tbool)] branch_cast_int) = OK (branch_cast_int, []).
Proof. vm_compute; reflexivity. Qed.
Example cast_outer_annotation_mismatch_rejected :
  branch_cast_rejected (branch_cast_check (Prim (Cast (Vtype Tbool)) [branch_cast_zero] branch_cast_int)).
Proof. vm_compute; exact I. Qed.
Example asymmetric_conditional_effects_accepted :
  branch_cast_check (Cond (Const (ConsBool true) (Vtype Tbool))
    (Prim Massgn [branch_cast_pointer; branch_cast_zero] Utype) (Unit Utype) Utype) = OK (Utype, [Write]).
Proof. vm_compute; reflexivity. Qed.
Example asymmetric_conditional_effects_typed : forall env Gamma Sigma,
  type_expr env Gamma Sigma branch_cast_pointer [] branch_cast_ref ->
  type_expr env Gamma Sigma
    (Cond (Const (ConsBool true) (Vtype Tbool))
      (Prim Massgn [branch_cast_pointer; branch_cast_zero] Utype) (Unit Utype) Utype) [Write] Utype.
Proof.
  intros env Gamma Sigma Hpointer.
  eapply ty_cond with (ef1 := []) (ef2 := [Write]) (ef3 := []) (branch_effect := [Write]).
  - constructor.
  - change [Write] with ([] ++ [] ++ [Write]). eapply ty_massgn;
      [exact Hpointer | reflexivity | reflexivity | constructor].
  - constructor.
  - reflexivity.
  - reflexivity.
Qed.
Example conditional_wrong_result_rejected :
  branch_cast_rejected (branch_cast_check (Cond (Const (ConsBool true) (Vtype Tbool))
    (Unit Utype) (Unit Utype) branch_cast_int)).
Proof. vm_compute; exact I. Qed.
Print Assumptions checked_cast_typing.
Print Assumptions checked_conditional_typing.
Print Assumptions asymmetric_conditional_effects_typed.
