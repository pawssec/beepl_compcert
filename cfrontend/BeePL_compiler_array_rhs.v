(* Array initializers consume translated rvalues directly. Wrapping an already
   translated scalar value in Evalof would require it to evaluate as an lvalue. *)
Require Import List String ZArith Integers AST Maps Errors SimplExpr Ctypes Csyntax Csem Cstrategy Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Require Import BeeTypes BeePL BeePL_values BeePL_Csyntax.
Import ListNotations.

Definition array_assignment_head id arrayty elementty index rhs :=
  Sdo(Eassign
    (Ederef(Ebinop Cop.Oadd (Evalof(Evar id arrayty)arrayty)
      (Eval(Values.Vint(Int.repr index)) tint)(tptr elementty))elementty)
    rhs (typeof rhs)).

Lemma array_init_from_keeps_translated_rhs : forall id element length attr index rhs rest stmt g g' inc,
  array_init_from id (Tarray element length attr) index (rhs::rest) g=Res stmt g' inc ->
  exists tail g1 i1,
    array_init_from id (Tarray element length attr) (index+1) rest g=Res tail g1 i1 /\
    stmt=Ssequence(array_assignment_head id (Tarray element length attr) element index rhs)tail.
Proof.
  intros id element length attr index rhs rest stmt g g' inc H.
  cbn [array_init_from get_carray_elm_ty] in H.
  cbv beta iota zeta delta [SimplExpr.bind ret] in H.
  destruct(array_init_from id (Tarray element length attr)(index+1)rest g)
    as [err|tail g1 i1] eqn:E; simpl in H; try discriminate.
  inversion H; subst. exists tail,g',i1; split; reflexivity.
Qed.

Lemma array_init_keeps_translated_rhs : forall id element length attr rhs rest stmt g g' inc,
  array_init id (Tarray element length attr)(rhs::rest)g=Res stmt g' inc ->
  exists tail g1 i1,
    array_init_from id (Tarray element length attr) 1 rest g=Res tail g1 i1 /\
    stmt=Ssequence(array_assignment_head id (Tarray element length attr)element 0 rhs)tail.
Proof.
  intros id element length attr rhs rest stmt g g' inc H.
  cbn [array_init get_carray_elm_ty] in H.
  cbv beta iota zeta delta [SimplExpr.bind ret] in H.
  destruct(array_init_from id (Tarray element length attr)1 rest g)
    as [err|tail g1 i1] eqn:E; simpl in H; try discriminate.
  inversion H; subst. exists tail,g',i1; split; reflexivity.
Qed.

Example scalar_literal_array_initializer_shape : forall id g,
  exists inc,
    array_init id (Tarray tint 1 noattr)[Eval(Values.Vint(Int.repr 41))tint]g=
      Res(Ssequence(array_assignment_head id (Tarray tint 1 noattr)tint 0
        (Eval(Values.Vint(Int.repr 41))tint))Sskip)g inc.
Proof. intros; eexists; reflexivity. Qed.

Lemma double_read_of_literal_cannot_evaluate : forall ge env m value ty trace final result,
  ~Cstrategy.eval_expression ge env m (Evalof(Eval value ty)ty)trace final result.
Proof.
  intros ge env m value ty trace final result H.
  inversion H; subst.
  match goal with Hstep:Cstrategy.eval_expr _ _ _ RV (Evalof _ _) _ _ _ |- _ =>
    inversion Hstep; subst end;
  match goal with Hbad:Cstrategy.eval_expr _ _ _ LV (Eval _ _) _ _ _ |- _ =>
    inversion Hbad end.
Qed.

Print Assumptions array_init_keeps_translated_rhs.
Print Assumptions scalar_literal_array_initializer_shape.
Print Assumptions double_read_of_literal_cannot_evaluate.
