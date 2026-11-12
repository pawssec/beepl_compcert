(* Structural induction cases. No recursive safety assumption is imposed on
   the parent: only the literal immediate-child induction hypothesis is used. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_initialized_runtime.
Require Import BeePL_coherent_configurations BeePL_coherent_scope_cases BeePL_coherent_option_cases.
Require Import BeePL_coherent_match_cases BeePL_coherent_control BeePL_coherent_loops.
Import ListNotations.

Ltac program_case_start :=
 unfold program_expression_safe; split;
 unfold program_expression_progress, program_expression_preservation;
 intros;
 match goal with Hp : program_runtime_configuration _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let Hcode := fresh "Hcode" in let Hconfig := fresh "Hconfig" in
  let Hheap := fresh "Hheap" in let Htyped := fresh "Htyped" in
  let Hlocations := fresh "Hlocations" in let Hframes := fresh "Hframes" in
  let Hcoherent := fresh "Hcoherent" in let Hann := fresh "Hannotation" in
  pose proof Hp as [Hcode Hconfig];
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent];
  pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hann;
  simpl in Hann; subst
 end.

Ltac program_child_progress_tac :=
 intros; eapply program_child_progress; eassumption.
Ltac program_child_preservation_tac :=
 intros;
 match goal with Hs:ssem_expr _ _ _ _ ?operand _ _ _,
 Hc:coherent_runtime_configuration _ _ _ _ _ _ _ _ ?operand _ _ |- _ =>
 eapply (program_child_preservation operand);[eassumption|eassumption|exact Hc|exact Hs]
 end.

Theorem program_bind_case : forall x tx init body rt,
 program_expression_safe init -> program_expression_safe(Bind x tx init body rt).
Proof.
 intros x tx init body rt Hchild. program_case_start.
 - right. eapply coherent_bind_progress_from_initializer;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_bind_preservation_from_initializer;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_callframe_case : forall callee body rt,
 program_expression_safe body -> program_expression_safe(CallFrame callee body rt).
Proof.
 intros callee body rt Hchild. program_case_start.
 - right. eapply coherent_callframe_progress_from_body;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_callframe_preservation_from_body;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_conditional_case : forall guard yes no rt,
 program_expression_safe guard -> program_expression_safe(Cond guard yes no rt).
Proof.
 intros guard yes no rt Hchild. program_case_start.
 - right. eapply coherent_conditional_progress_from_guard;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_conditional_preservation_from_guard;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_some_case : forall operand rt,
 program_expression_safe operand -> program_expression_safe(Esome operand rt).
Proof.
 intros operand rt Hchild. program_case_start.
 - right. eapply coherent_some_progress_from_operand;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_some_preservation_from_operand;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_match_case : forall operand patterns branches rt,
 program_expression_safe operand -> program_expression_safe(Match operand patterns branches rt).
Proof.
 intros operand patterns branches rt Hchild. program_case_start.
 - right. eapply coherent_match_progress_from_scrutinee;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_match_preservation_from_scrutinee;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_loopframe_case : forall remaining template active,
 program_expression_safe active -> program_expression_safe(LoopFrame remaining template active).
Proof.
 intros remaining template active Hchild. program_case_start.
 - right. eapply coherent_loop_frame_progress_from_body;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_loop_frame_preservation_from_body;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.
Print Assumptions program_callframe_case.
Print Assumptions program_match_case.
