(* Array, field, and source-loop constructor cases. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_program_control_cases.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_field_induction BeePL_coherent_array_cases BeePL_coherent_for_cases.
Import ListNotations.

Theorem program_field_case : forall operand field rt,
 program_expression_safe operand -> program_expression_safe(Sfield operand field rt).
Proof.
 intros operand field rt Hchild;program_case_start.
 - right. eapply coherent_field_progress_from_operand;[exact Hconfig|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_field_preservation_from_operand;[exact Hconfig|program_child_preservation_tac|eassumption].
Qed.

Theorem program_for_case : forall first last dir body rt,
 program_expression_safe first -> program_expression_safe last ->
 program_expression_safe(For first last dir body rt).
Proof.
 intros first last dir body rt Hfirst Hlast;program_case_start.
 - right. eapply coherent_for_progress_from_bounds;[exact Hconfig|program_child_progress_tac|program_child_progress_tac].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_for_preservation_from_bounds;[exact Hconfig|program_child_preservation_tac|program_child_preservation_tac|eassumption].
Qed.

Theorem program_array_case : forall arr ty es rt,
 Forall program_expression_safe es -> program_expression_safe(Ainit arr ty es rt).
Proof.
 intros arr ty es rt Hchildren;program_case_start.
 all: inversion Htyped;subst.
 - right. eapply coherent_ainit_progress_from_members;[reflexivity|exact Hconfig|].
   intros e Hin effect elementType Hchild.
   eapply program_child_progress;[exact(proj1(Forall_forall _ _) Hchildren e Hin)|eassumption|exact Hchild].
 - eapply program_result_lift;[eassumption|].
   eapply coherent_ainit_preservation_from_members;[reflexivity|exact Hconfig| |eassumption].
   intros e Hin effect elementType Hchild nextM nextVm nextElement Hs.
   eapply program_child_preservation;[exact(proj1(Forall_forall _ _) Hchildren e Hin)|eassumption|exact Hchild|exact Hs].
Qed.
