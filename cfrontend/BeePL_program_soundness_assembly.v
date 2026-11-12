(* Whole-expression structural assembly. The first theorem isolates the call
   obligation; the final theorem below discharges it constructively. Initial
   loader adequacy and compiler simulation are separate from state soundness. *)
Require Import List.
Require Import BeePL BeePL_program_induction BeePL_program_control_cases.
Require Import BeePL_program_leaf_cases BeePL_program_composite_cases.
Require Import BeePL_program_primitive_case BeePL_program_structure_case.
Require Import BeePL_program_application_case.
Import ListNotations.

Theorem program_expression_soundness_given_calls :
 evaluated_application_obligation -> forall e,program_expression_safe e.
Proof.
 intros Hcalls.
 apply (@expr_mut_ind program_expression_safe (Forall program_expression_safe)).
 constructor;intros;
 eauto using Forall_nil,Forall_cons,
 program_value_case,program_variable_case,program_constant_case,
 program_application_case,program_primitive_case,program_conditional_case,
 program_bind_case,program_unit_case,program_address_case,program_structure_case,
 program_field_case,program_for_case,program_none_case,program_some_case,
 program_match_case,program_ebytes_case,program_array_case,program_named_array_case,
 program_callframe_case,program_loopframe_case.
Qed.
Print Assumptions program_expression_soundness_given_calls.

Require Import BeePL_general_application.
Require Import BeePL_program_runtime BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_typesystem.

Lemma evaluated_application_obligation_discharged : evaluated_application_obligation.
Proof.
 intros value annotation args result Hvalues. program_case_start.
 - right. eapply general_application_progress;eassumption.
 - eapply general_application_preservation;eassumption.
Qed.

Theorem program_expression_soundness : forall e,program_expression_safe e.
Proof.
 apply program_expression_soundness_given_calls.
 exact evaluated_application_obligation_discharged.
Qed.

Theorem program_expression_progress_checked : forall e,program_expression_progress e.
Proof. intros e;exact(proj1(program_expression_soundness e)). Qed.

Theorem program_expression_preservation_checked : forall e,program_expression_preservation e.
Proof. intros e;exact(proj2(program_expression_soundness e)). Qed.

Print Assumptions program_expression_soundness.
Print Assumptions program_expression_progress_checked.
Print Assumptions program_expression_preservation_checked.
