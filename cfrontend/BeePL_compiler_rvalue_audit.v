(* Executable Csyntax's lvalue/rvalue distinction is not a proof-only
   normalization convention. Bare lvalues lack an RV derivation independently
   of memory contents; the corrected compiler emits executable read forms. *)
Require Import List String Integers AST Maps Errors SimplExpr Ctypes Csyntax Csem Cstrategy.
Require Import BeeTypes BeePL BeePL_values BeePL_Csyntax BeePL_compiler_bindings BeePL_compiler_decomposition.

Lemma compiler_bound_value_from_storage : forall read_variable env source target ty,
  compiler_bound_storage env source = Some target ->
  compiler_bound_value read_variable env source ty = read_variable target ty.
Proof.
  intros read_variable env source target ty H.
  unfold compiler_bound_storage in H; unfold compiler_bound_value.
  destruct (PTree.get source env) as [[slot|]|]; inversion H; reflexivity.
Qed.

Lemma bare_variable_has_no_rvalue_evaluation : forall ge env m id ty trace final value,
  ~ Cstrategy.eval_expression ge env m (Evar id ty) trace final value.
Proof.
  intros ge env m id ty trace final value H.
  inversion H; subst. match goal with
  | Hstep : Cstrategy.eval_expr _ _ _ RV (Evar _ _) _ _ _ |- _ => inversion Hstep
  end.
Qed.

Lemma bare_dereference_has_no_rvalue_evaluation : forall ge env m pointer ty trace final value,
  ~ Cstrategy.eval_expression ge env m (Ederef pointer ty) trace final value.
Proof.
  intros ge env m pointer ty trace final value H.
  inversion H; subst. match goal with
  | Hstep : Cstrategy.eval_expr _ _ _ RV (Ederef _ _) _ _ _ |- _ => inversion Hstep
  end.
Qed.

(* The current compiler now emits a real rvalue. Its unit case does not
   attempt to read nonexistent void storage. *)
Lemma variable_lowering_success_witness : forall id ty ctx bctx g,
  exists inc,
    transBeePL_expr_expr (Var id ty) ctx bctx g=
      Res(trans_bound_variable bctx id ty,ctx,bctx)g inc.
Proof. intros; eexists; reflexivity. Qed.

Theorem actual_unit_variable_lowering_evaluates :
  forall id ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr (Var id Utype) ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  forall ge env m,
  Cstrategy.eval_expression ge env m ce Events.E0 m (trans_bvalue_cvalue Vunit).
Proof.
  intros id ctx bctx ce ctx' bctx' g g' inc H ge env m.
  pose proof (proj1 expression_translation_decomposition _ _ _ _ _ _ _ _ _ H) as D.
  cbn in D. destruct D as [-> _].
  unfold trans_bound_variable, compiler_bound_value.
  destruct (PTree.get id (lexical_bindings bctx)) as [[slot|]|];
    econstructor; constructor.
Qed.

Theorem actual_nonunit_variable_lowering_evaluates :
  forall id ty ctx bctx ce ctx' bctx' g g' inc,
  transBeePL_expr_expr (Var id ty) ctx bctx g=Res(ce,ctx',bctx')g' inc ->
  ty<>Utype -> forall target,
  compiler_bound_storage (lexical_bindings bctx) id = Some target ->
  forall ge env m block value,
  Cstrategy.eval_simple_lvalue ge env m (Evar target(transBeePL_type ty)) block Ptrofs.zero Full ->
  type_is_volatile(transBeePL_type ty)=false ->
  Csem.deref_loc ge (transBeePL_type ty) m block Ptrofs.zero Full Events.E0 value ->
  Cstrategy.eval_expression ge env m ce Events.E0 m value.
Proof.
  intros id ty ctx bctx ce ctx' bctx' g g' inc H Hnonunit target Hstorage ge env m block value Hloc Hvol Hread.
  pose proof (proj1 expression_translation_decomposition _ _ _ _ _ _ _ _ _ H) as D.
  cbn in D. destruct D as [-> _].
  unfold trans_bound_variable.
  rewrite (compiler_bound_value_from_storage _ _ _ _ _ Hstorage).
  assert (E : trans_variable_rvalue target ty=
    Evalof(Evar target(transBeePL_type ty))(transBeePL_type ty)).
  { destruct ty; [contradiction|..]; reflexivity. }
  rewrite E. eapply Cstrategy.eval_expression_intro.
  - apply Cstrategy.eval_valof; [exact Hvol|constructor].
  - eapply Cstrategy.esr_rvalof; [exact Hloc|reflexivity|exact Hvol|exact Hread].
Qed.

Lemma corrected_dereference_expression_reads : forall ge env m operand trace final block ofs ty value,
  Cstrategy.eval_expression ge env m operand trace final (Values.Vptr block ofs) ->
  type_is_volatile ty=false ->
  Csem.deref_loc ge ty final block ofs Full Events.E0 value ->
  Cstrategy.eval_expression ge env m (Evalof(Ederef operand ty)ty) trace final value.
Proof.
  intros ge env m operand trace final block ofs ty value Heval Hvol Hread.
  inversion Heval; subst.
  eapply Cstrategy.eval_expression_intro.
  - apply Cstrategy.eval_valof; [exact Hvol|]. eapply Cstrategy.eval_deref; eassumption.
  - eapply Cstrategy.esr_rvalof; [|reflexivity|exact Hvol|exact Hread].
    apply Cstrategy.esl_deref; eassumption.
Qed.

Print Assumptions bare_variable_has_no_rvalue_evaluation.
Print Assumptions bare_dereference_has_no_rvalue_evaluation.
Print Assumptions actual_unit_variable_lowering_evaluates.
Print Assumptions actual_nonunit_variable_lowering_evaluates.
Print Assumptions corrected_dereference_expression_reads.
