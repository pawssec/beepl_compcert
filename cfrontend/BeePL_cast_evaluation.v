(* Compositional simulation of the generated primitive cast context.
   Operand evaluation is an explicit premise: this does not assume or claim
   the unfinished whole-compiler simulation theorem. *)
Require Import List Integers AST Memory Ctypes Csyntax Csem Cstrategy Cop Errors Events.
Require Import BeeTypes BeePL_values BeePL BeePL_mem BeePL_Csyntax Type_proof_C.
Require Import BeePL_bool_cast_compiler.

Lemma cast_successful_value_encoding : forall raw v,
  trans_cvalue_bvalue raw = OK v -> trans_bvalue_cvalue v = raw.
Proof.
  intros raw v Hdecode. destruct raw; simpl in Hdecode; try discriminate;
    inversion Hdecode; reflexivity.
Qed.

Lemma generated_cast_context_evaluation : forall ge env m operand tr final reduced target,
  eval_expr ge env m RV operand tr final reduced ->
  eval_expr ge env m RV (trans_cast_expression target operand) tr final
    (trans_cast_expression target reduced).
Proof.
  intros ge env m operand tr final reduced target Hstep.
  destruct target; simpl; try (apply eval_cast; exact Hstep).
  destruct p; simpl; try (apply eval_cast; exact Hstep).
  apply eval_cast.
  replace tr with (tr ++ E0) at 1 by (unfold E0; apply app_nil_r).
  eapply eval_binop; [apply eval_cast; exact Hstep | apply eval_val].
Qed.

Theorem generated_primitive_cast_evaluation :
  forall ge env m operand tr final cv target raw result,
  eval_expression ge env m operand tr final cv ->
  Cop.sem_cast cv (Csyntax.typeof operand) (transBeePL_type (Vtype target)) final = Some raw ->
  decode_memory_value (Vtype target) raw = OK result ->
  eval_expression ge env m (trans_cast_expression (Vtype target) operand)
    tr final (trans_bvalue_cvalue result).
Proof.
  intros ge env m operand tr final cv target raw result Heval Hcast Hdecode.
  inversion Heval as [env0 m0 operand0 tr0 final0 reduced cv0 Hreduce Hsimple]; subst.
  pose proof (c_eval_expr_type_preservation operand ge env m reduced tr final Hreduce) as Htype.
  eapply eval_expression_intro with
    (a' := trans_cast_expression (Vtype target) reduced).
  - apply generated_cast_context_evaluation. exact Hreduce.
  - destruct target.
    + eapply generated_bool_cast_normalizes; [exact Hsimple | | exact Hdecode].
      rewrite <- Htype. exact Hcast.
    + simpl in Hdecode. simpl. eapply esr_cast; [exact Hsimple |].
      rewrite (cast_successful_value_encoding _ _ Hdecode), <- Htype. exact Hcast.
    + simpl in Hdecode. simpl. eapply esr_cast; [exact Hsimple |].
      rewrite (cast_successful_value_encoding _ _ Hdecode), <- Htype. exact Hcast.
Qed.

Print Assumptions generated_cast_context_evaluation.
Print Assumptions generated_primitive_cast_evaluation.
