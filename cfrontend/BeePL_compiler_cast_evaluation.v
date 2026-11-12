(* Connect actual successful evaluated-operand lowering to the already checked
   compositional primitive-cast semantics. No operand execution or final-state
   simulation oracle is needed for an evaluated source value. *)
Require Import List String ZArith Integers AST Maps Errors SimplExpr Ctypes Csyntax Cstrategy Events Cop.
Require Import BeeTypes BeePL_values BeePL BeePL_mem BeePL_Csyntax.
Require Import BeePL_compiler_decomposition BeePL_cast_evaluation.
Import ListNotations.

Lemma evaluated_cast_translation_shape : forall source target value ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr
    (Prim(Cast(Vtype target))[Val value(Vtype source)](Vtype target)) ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  ce=trans_cast_expression(Vtype target)
    (Eval(trans_bvalue_cvalue value)(transBeePL_type(Vtype source))) /\
  ctx'=ctx /\ bctx'=bctx.
Proof.
  intros source target value ctx bctx ce ctx' bctx' g g' inc H.
  pose proof (proj1 expression_translation_decomposition _ _ _ _ _ _ _ _ _ H) as D.
  cbn [fst snd] in D.
  destruct D as [ces [g1 [i1 [Hlist Hce]]]].
  cbv beta iota zeta delta [transBeePL_expr_exprs transBeePL_expr_expr
    SimplExpr.bind2 SimplExpr.bind ret fst snd] in Hlist.
  inversion Hlist; subst. repeat split; reflexivity.
Qed.

Theorem successful_evaluated_primitive_cast_evaluation :
  forall ge env m source target value raw result ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr
    (Prim(Cast(Vtype target))[Val value(Vtype source)](Vtype target)) ctx bctx g=
      Res(ce,ctx',bctx')g' inc ->
  Cop.sem_cast (trans_bvalue_cvalue value) (transBeePL_type(Vtype source))
    (transBeePL_type(Vtype target)) m=Some raw ->
  decode_memory_value (Vtype target) raw=OK result ->
  Cstrategy.eval_expression ge env m ce E0 m (trans_bvalue_cvalue result).
Proof.
  intros ge env m source target value raw result ctx bctx ce ctx' bctx' g g' inc
    Htranslate Hcast Hdecode.
  destruct(evaluated_cast_translation_shape _ _ _ _ _ _ _ _ _ _ _ Htranslate)
    as [Hshape _]. rewrite Hshape.
  eapply generated_primitive_cast_evaluation; [|exact Hcast|exact Hdecode].
  econstructor; constructor.
Qed.

(* The concrete Boolean behavior is forced by the real compiler output:
   2 becomes the canonical encoded true, and 256 truncates to zero first. *)
Example compiled_bool_two_is_one : forall ge env m ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr
    (Prim(Cast(Vtype Tbool))
      [Val(Vint(Int.repr 2))(Vtype(Tint I32 Signed Ctypes.noattr))](Vtype Tbool)) ctx bctx g=
    Res(ce,ctx',bctx')g' inc ->
  Cstrategy.eval_expression ge env m ce E0 m (Values.Vint Int.one).
Proof.
  intros. change (Cstrategy.eval_expression ge env m ce E0 m
    (trans_bvalue_cvalue(Vbool true))).
  eapply successful_evaluated_primitive_cast_evaluation; [exact H|reflexivity|reflexivity].
Qed.

Example compiled_bool_256_is_zero : forall ge env m ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr
    (Prim(Cast(Vtype Tbool))
      [Val(Vint(Int.repr 256))(Vtype(Tint I32 Signed Ctypes.noattr))](Vtype Tbool)) ctx bctx g=
    Res(ce,ctx',bctx')g' inc ->
  Cstrategy.eval_expression ge env m ce E0 m (Values.Vint Int.zero).
Proof.
  intros. change (Cstrategy.eval_expression ge env m ce E0 m
    (trans_bvalue_cvalue(Vbool false))).
  eapply successful_evaluated_primitive_cast_evaluation; [exact H|reflexivity|reflexivity].
Qed.

Print Assumptions successful_evaluated_primitive_cast_evaluation.
Print Assumptions compiled_bool_two_is_one.
Print Assumptions compiled_bool_256_is_zero.
