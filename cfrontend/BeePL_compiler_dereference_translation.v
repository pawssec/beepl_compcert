(* Compositional primitive dereference for actual generated expressions.
   The child evaluation is the induction hypothesis; the enclosing target
   dereference execution is derived from the source read and memory injection. *)
Require Import List String AST Maps Errors Integers Values Memory Events SimplExpr.
Require Import Ctypes Csyntax Csem Cstrategy BeeTypes BeePL_values BeePL BeePL_Csyntax.
Require Import BeePL_compiler_decomposition BeePL_compiler_bool_read.
Require Import BeePL_compiler_variable_read BeePL_compiler_rvalue_audit.
Import ListNotations.

Lemma singleton_dereference_translation_shape :
  forall operand result ctx bctx ce ctx' bctx' g g' inc child childctx childbctx childg childinc,
  transBeePL_expr_expr (Prim Deref [operand] result) ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  transBeePL_expr_expr operand ctx bctx g=Res(child,childctx,childbctx)childg childinc ->
  ce=Evalof(Ederef child(transBeePL_type result))(transBeePL_type result) /\
  ctx'=childctx /\ bctx'=childbctx.
Proof.
  intros operand result ctx bctx ce ctx' bctx' g g' inc child childctx childbctx childg childinc
    Hparent Hchild.
  pose proof(proj1 expression_translation_decomposition _ _ _ _ _ _ _ _ _ Hparent) as D.
  cbn in D. destruct D as [ces [g1 [i1 [Hlist Hce]]]].
  cbv beta iota zeta delta [transBeePL_expr_exprs SimplExpr.bind2 SimplExpr.bind ret fst snd] in Hlist.
  rewrite Hchild in Hlist.
  cbv beta iota zeta delta [transBeePL_expr_exprs SimplExpr.bind2 SimplExpr.bind ret fst snd] in Hlist.
  inversion Hlist; subst. repeat split; reflexivity.
Qed.

Theorem compiled_primitive_dereference_from_child :
  forall ge env f sourcefinal targetinitial targetfinal operand pt value
    sourceblock sourceoffset targetblock targetoffset trace
    ctx bctx ce ctx' bctx' g g' inc child childctx childbctx childg childinc,
  transBeePL_expr_expr (Prim Deref [operand](Vtype pt))ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  transBeePL_expr_expr operand ctx bctx g=Res(child,childctx,childbctx)childg childinc ->
  Cstrategy.eval_expression ge env targetinitial child trace targetfinal
    (Values.Vptr targetblock targetoffset) ->
  surface_primitive_read pt -> typeof_value value(Vtype pt) ->
  deref_addr(Vtype pt)sourcefinal sourceblock sourceoffset Full value ->
  Mem.inject f sourcefinal targetfinal ->
  Val.inject f (Values.Vptr sourceblock sourceoffset)(Values.Vptr targetblock targetoffset) ->
  exists targetvalue,
    Val.inject f (trans_bvalue_cvalue value)targetvalue /\
    Cstrategy.eval_expression ge env targetinitial ce trace targetfinal targetvalue.
Proof.
  intros ge env f sourcefinal targetinitial targetfinal operand pt value
    sourceblock sourceoffset targetblock targetoffset trace
    ctx bctx ce ctx' bctx' g g' inc child childctx childbctx childg childinc
    Hparent Hchild Heval Hsurface Hshape Hread Hinj Hptr.
  destruct(singleton_dereference_translation_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hparent Hchild)
    as [Hce _].
  destruct(injected_surface_primitive_read_location ge _ _ _ _ _ _ _ _ _
    Hsurface Hshape Hinj Hptr Hread) as [loaded [Hvalue [Hvol Htarget]]].
  exists loaded; split; [exact Hvalue|]. rewrite Hce.
  eapply corrected_dereference_expression_reads; eauto.
Qed.

Print Assumptions singleton_dereference_translation_shape.
Print Assumptions compiled_primitive_dereference_from_child.
