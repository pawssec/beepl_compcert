(* Ordinary memory operations carry the nonvolatile contract in their typing
   derivation. The executable checker must establish the same contract. *)
Require Import List Bool Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker.
Require Import BeePL_type_equality.
Import ListNotations.

Lemma reference_typing_nonvolatile : forall env Gamma Sigma operand basic attr ef ty,
  type_expr env Gamma Sigma
    (Prim Ref [operand] (Ptrtype (Reftype basic attr))) ef ty ->
  type_is_volatile (transBeePL_type (construct_type_btype basic)) = false.
Proof. intros; inversion H; subst; assumption. Qed.

Lemma dereference_typing_nonvolatile : forall env Gamma Sigma operand annotation ef ty,
  type_expr env Gamma Sigma (Prim Deref [operand] annotation) ef ty ->
  type_is_volatile (transBeePL_type ty) = false.
Proof. intros; inversion H; subst; assumption. Qed.

Lemma assignment_typing_nonvolatile : forall env Gamma Sigma lhs rhs annotation ef ty,
  type_expr env Gamma Sigma (Prim Massgn [lhs; rhs] annotation) ef ty ->
  type_is_volatile (transBeePL_type (typeof_expr rhs)) = false.
Proof.
  intros env Gamma Sigma lhs rhs annotation ef ty Htyped.
  inversion Htyped; subst.
  match goal with Hrhs : type_expr _ _ _ rhs _ _ |- _ =>
    rewrite (type_rel_typeof _ _ _ _ _ _ Hrhs); assumption
  end.
Qed.

Theorem checked_reference_typing : forall env Gamma Sigma operand annotation result effects,
  (forall ty ef, type_check_expr env Gamma Sigma operand = OK (ty, ef) ->
    type_expr env Gamma Sigma operand ef ty) ->
  type_check_expr env Gamma Sigma (Prim Ref [operand] annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Prim Ref [operand] annotation) effects result.
Proof.
  intros env Gamma Sigma operand annotation result effects Hchild Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_expr env Gamma Sigma operand) as [[operandType operandEffects]|err] eqn:Hoperand;
    cbn in Hcheck; try discriminate.
  destruct operandType as [|prim|ptr|sid attr|elem len attr|args eff rt va|]; try discriminate.
  fold (transBeePL_type (Vtype prim)) in Hcheck.
  destruct (type_is_volatile (transBeePL_type (Vtype prim))) eqn:Hvolatile; try discriminate.
  destruct (eq_type annotation (Ptrtype (Reftype (Bprim prim) (attr_of_primitive_type prim))))
    eqn:Hannotation; try discriminate.
  apply eq_type_sound in Hannotation. subst annotation.
  inversion Hcheck; subst. eapply ty_ref; [eapply Hchild; reflexivity |exact Hvolatile].
Qed.

Theorem checked_dereference_typing : forall env Gamma Sigma operand annotation result effects,
  (forall ty ef, type_check_expr env Gamma Sigma operand = OK (ty, ef) ->
    type_expr env Gamma Sigma operand ef ty) ->
  type_check_expr env Gamma Sigma (Prim Deref [operand] annotation) = OK (result, effects) ->
  type_expr env Gamma Sigma (Prim Deref [operand] annotation) effects result.
Proof.
  intros env Gamma Sigma operand annotation result effects Hchild Hcheck.
  cbn [type_check_expr] in Hcheck.
  destruct (type_check_expr env Gamma Sigma operand) as [[operandType operandEffects]|err] eqn:Hoperand;
    cbn in Hcheck; try discriminate.
  destruct operandType as [|prim|ptr|sid attr|elem len attr|args eff rt va|]; try discriminate.
  destruct (eq_type annotation (get_data_type ptr)) eqn:Hannotation; try discriminate.
  destruct (is_option_ptr_type ptr) eqn:Hoption; cbn in Hcheck; try discriminate.
  destruct (type_is_volatile (transBeePL_type (get_data_type ptr))) eqn:Hvolatile; try discriminate.
  apply eq_type_sound in Hannotation. subst annotation.
  inversion Hcheck; subst. eapply ty_deref; eauto.
Qed.

Print Assumptions reference_typing_nonvolatile.
Print Assumptions dereference_typing_nonvolatile.
Print Assumptions assignment_typing_nonvolatile.
Print Assumptions checked_reference_typing.
Print Assumptions checked_dereference_typing.
