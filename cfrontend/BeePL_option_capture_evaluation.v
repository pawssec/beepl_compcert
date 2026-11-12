(* Actual target-language evaluation of one scrutinee capture. This composes
   with a continuation evaluation hypothesis; it is not whole-compiler
   simulation. The caller must allocate a fresh temporary, establish its
   environment binding, and keep it writable across scrutinee evaluation. *)
Require Import Coqlib List ZArith Integers AST Maps Memory Ctypes Csyntax.
Require Import Csem Cstrategy Cop Events Values.
Local Open Scope Z_scope.

Theorem capture_expression_once : forall ge env initial operand tr evaluated value
    temp block ty chunk saved_value,
  eval_expression ge env initial operand tr evaluated value ->
  PTree.get temp env = Some (block,ty) ->
  access_mode ty = By_value chunk -> type_is_volatile ty = false ->
  Cop.sem_cast value (Csyntax.typeof operand) ty evaluated = Some saved_value ->
  Mem.valid_access evaluated chunk block 0 Writable ->
  Val.load_result chunk saved_value = saved_value ->
  exists saved,
    Mem.store chunk evaluated block 0 saved_value = Some saved /\
    eval_expr ge env initial RV (Eassign (Evar temp ty) operand ty)
      tr saved (Eval saved_value ty) /\
    eval_expression ge env saved (Evalof (Evar temp ty) ty) E0 saved saved_value.
Proof.
  intros ge env initial operand tr evaluated value temp block ty chunk saved_value
    Heval Henv Hmode Hvolatile Hcast Haccess Hnormalize.
  inversion Heval as [env0 m0 a0 trace0 final0 reduced v0 Hreduce Hsimple]; subst.
  destruct (Mem.valid_access_store _ _ _ _ saved_value Haccess) as [saved Hstore].
  exists saved; split; [exact Hstore|]. split.
  - replace tr with (E0 ** tr ** E0) by (unfold E0, Eapp; simpl; apply app_nil_r).
    eapply eval_assign with (l' := Evar temp ty) (r' := reduced)
      (v := value) (v1 := saved_value) (b := block) (ofs := Ptrofs.zero) (bf := Full).
    + constructor.
    + exact Hreduce.
    + apply esl_var_local; exact Henv.
    + exact Hsimple.
    + exact Hcast.
    + eapply assign_loc_value; [exact Hmode|exact Hvolatile|exact Hstore].
    + reflexivity.
  - eapply eval_expression_intro with (a' := Evalof (Evar temp ty) ty).
    + apply eval_valof; [exact Hvolatile|constructor].
    + eapply esr_rvalof; [apply esl_var_local; exact Henv|reflexivity|exact Hvolatile|].
      eapply deref_loc_value; [exact Hmode|exact Hvolatile|].
      change (Mem.load chunk saved block 0 = Some saved_value).
      rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore), Hnormalize. reflexivity.
Qed.

Theorem captured_comma_evaluation : forall ge env initial operand tr evaluated value
    temp block ty chunk saved_value,
  eval_expression ge env initial operand tr evaluated value ->
  PTree.get temp env = Some (block,ty) ->
  access_mode ty = By_value chunk -> type_is_volatile ty = false ->
  Cop.sem_cast value (Csyntax.typeof operand) ty evaluated = Some saved_value ->
  Mem.valid_access evaluated chunk block 0 Writable ->
  Val.load_result chunk saved_value = saved_value ->
  exists saved,
    Mem.store chunk evaluated block 0 saved_value = Some saved /\
    eval_expression ge env saved (Evalof (Evar temp ty) ty) E0 saved saved_value /\
    forall continuation trace final result,
      eval_expression ge env saved continuation trace final result ->
      eval_expression ge env initial
        (Ecomma (Eassign (Evar temp ty) operand ty) continuation (Csyntax.typeof continuation))
        (tr ** trace) final result.
Proof.
  intros * Heval Henv Hmode Hvolatile Hcast Haccess Hnormalize.
  destruct (capture_expression_once _ _ _ _ _ _ _ _ _ _ _ _ Heval Henv Hmode Hvolatile Hcast Haccess Hnormalize)
    as [saved [Hstore [Hcapture Hread]]].
  exists saved; split; [exact Hstore|]. split; [exact Hread|].
  intros continuation trace final result Hcontinuation.
  inversion Hcontinuation as [env0 m0 a0 trace0 final0 reduced v0 Hreduce Hsimple]; subst.
  eapply eval_expression_intro; [|exact Hsimple].
  eapply eval_comma; [exact Hcapture|constructor|exact Hreduce|reflexivity].
Qed.

Lemma optional_pointer_capture_normalizes : forall b offset,
  Val.load_result Mptr (Vptr b offset) = Vptr b offset.
Proof. intros; unfold Mptr; destruct Archi.ptr64 eqn:Harch; simpl; rewrite ?Harch; reflexivity. Qed.
Lemma optional_null_capture_normalizes : Val.load_result Mptr Vnullptr = Vnullptr.
Proof. unfold Mptr, Vnullptr; destruct Archi.ptr64 eqn:Harch; simpl; rewrite ?Harch; reflexivity. Qed.

Print Assumptions capture_expression_once.
Print Assumptions captured_comma_evaluation.

Theorem captured_statement_sequence : forall ge env initial operand tr evaluated value
    temp block ty chunk saved_value,
  eval_expression ge env initial operand tr evaluated value ->
  PTree.get temp env = Some (block,ty) ->
  access_mode ty = By_value chunk -> type_is_volatile ty = false ->
  Cop.sem_cast value (Csyntax.typeof operand) ty evaluated = Some saved_value ->
  Mem.valid_access evaluated chunk block 0 Writable ->
  Val.load_result chunk saved_value = saved_value ->
  exists saved,
    Mem.store chunk evaluated block 0 saved_value = Some saved /\
    eval_expression ge env saved (Evalof (Evar temp ty) ty) E0 saved saved_value /\
    forall continuation trace final outcome,
      exec_stmt ge env saved continuation trace final outcome ->
      exec_stmt ge env initial
        (Ssequence (Sdo (Eassign (Evar temp ty) operand ty)) continuation)
        (tr ** trace) final outcome.
Proof.
  intros * Heval Henv Hmode Hvolatile Hcast Haccess Hnormalize.
  destruct (capture_expression_once _ _ _ _ _ _ _ _ _ _ _ _ Heval Henv Hmode Hvolatile Hcast Haccess Hnormalize)
    as [saved [Hstore [Hcapture Hread]]].
  exists saved; split; [exact Hstore|]. split; [exact Hread|].
  intros continuation trace final outcome Hcontinuation.
  eapply exec_Sseq_1; [|exact Hcontinuation].
  eapply exec_Sdo. eapply eval_expression_intro; [exact Hcapture|constructor].
Qed.
Print Assumptions captured_statement_sequence.
