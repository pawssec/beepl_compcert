(* Actual tail-call statement lowering preserves a non-unit call's result.
   The execution lemma composes with a child Ecall evaluation; it is not yet
   a source/target callee simulation theorem. *)
Require Import List String AST Errors Ctypes Csyntax Csem Cstrategy Events SimplExpr.
Require Import BeeTypes BeePL BeePL_Csyntax.
Import ListNotations.

Definition tail_call_statement (ty : BeeTypes.type) (callee : Csyntax.expr)
    (arguments : Csyntax.exprlist) : Csyntax.statement :=
  let call := Ecall callee arguments (transBeePL_type ty) in
  match ty with Utype => Sdo call | _ => Sreturn(Some call) end.

Theorem translated_tail_call_shape : forall env head args ty ctx bc g statement ctx' bc' g' proof,
  transBeePL_expr_st env (App head args ty) ctx bc g=Res(statement,ctx',bc')g' proof ->
  exists callee arguments,
    statement=tail_call_statement ty callee arguments.
Proof.
  intros env head args ty ctx bc g statement ctx' bc' g' proof H.
  cbn [transBeePL_expr_st] in H.
  unfold SimplExpr.bind2,SimplExpr.bind,SimplExpr.ret in H.
  destruct(transBeePL_expr_expr head ctx bc g) as [message|[[callee middle] bcm] gm im] eqn:Eh;
    cbn in H; try discriminate.
  destruct(transBeePL_expr_exprs transBeePL_expr_expr args middle bcm gm)
    as [message|[[arguments final] bcf] gf iff] eqn:Ea; cbn in H; try discriminate.
  inversion H; subst. exists callee,arguments. reflexivity.
Qed.

Theorem translated_nonunit_tail_call_shape : forall env head args ty ctx bc g statement ctx' bc' g' proof,
  ty<>Utype ->
  transBeePL_expr_st env (App head args ty) ctx bc g=Res(statement,ctx',bc')g' proof ->
  exists callee arguments,
    statement=Sreturn(Some(Ecall callee arguments(transBeePL_type ty))).
Proof.
  intros. destruct(translated_tail_call_shape _ _ _ _ _ _ _ _ _ _ _ _ H0)
    as [callee [arguments E]]. exists callee,arguments. rewrite E.
  unfold tail_call_statement. destruct ty; congruence.
Qed.

Theorem tail_call_statement_execution : forall ge env before after ty callee arguments trace value,
  eval_expression ge env before (Ecall callee arguments(transBeePL_type ty)) trace after value ->
  exec_stmt ge env before (tail_call_statement ty callee arguments) trace after
    (match ty with Utype => Out_normal
     | _ => Out_return(Some(value,transBeePL_type ty)) end).
Proof.
  intros. destruct ty; unfold tail_call_statement; simpl;
    [eapply exec_Sdo | eapply exec_Sreturn_some | eapply exec_Sreturn_some |
     eapply exec_Sreturn_some | eapply exec_Sreturn_some | eapply exec_Sreturn_some |
     eapply exec_Sreturn_some]; eassumption.
Qed.

Corollary translated_tail_call_execution : forall ge env before after cenv head args ty
    ctx bc g statement ctx' bc' g' proof,
  transBeePL_expr_st cenv (App head args ty) ctx bc g=Res(statement,ctx',bc')g' proof ->
  exists callee arguments,
    statement=tail_call_statement ty callee arguments /\
    forall trace value,
      eval_expression ge env before (Ecall callee arguments(transBeePL_type ty)) trace after value ->
      exec_stmt ge env before statement trace after
        (match ty with Utype => Out_normal
         | _ => Out_return(Some(value,transBeePL_type ty)) end).
Proof.
  intros. destruct(translated_tail_call_shape _ _ _ _ _ _ _ _ _ _ _ _ H)
    as [callee [arguments E]]. exists callee,arguments; split; [exact E|].
  intros. rewrite E. apply tail_call_statement_execution; assumption.
Qed.
Print Assumptions translated_tail_call_shape.
Print Assumptions translated_tail_call_execution.
