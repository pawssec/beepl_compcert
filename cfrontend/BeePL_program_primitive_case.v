(* All typed primitive operators in the mutual expression induction. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_initialized_runtime.
Require Import BeePL_coherent_configurations BeePL_coherent_operators BeePL_coherent_casts.
Require Import BeePL_reference_induction BeePL_memory_induction BeePL_coherent_array_cases.
Import ListNotations.

Ltac primitive_child_progress :=
 intros;
 repeat match goal with H : _ = _ \/ _ = _ |- _ => destruct H;subst end;
 eapply program_child_progress; eassumption.
Ltac primitive_child_preservation :=
 intros;
 repeat match goal with H : _ = _ \/ _ = _ |- _ => destruct H;subst end;
 match goal with Hs:ssem_expr _ _ _ _ ?operand _ _ _,
 Hc:coherent_runtime_configuration _ _ _ _ _ _ _ _ ?operand _ _ |- _ =>
 eapply (program_child_preservation operand);[eassumption|eassumption|exact Hc|exact Hs]
 end.
Ltac split_children :=
 repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H;clear H;subst end.

Theorem program_primitive_case : forall builtin args annotation,
 Forall program_expression_safe args -> program_expression_safe(Prim builtin args annotation).
Proof.
 intros builtin args annotation Hchildren. split.
 - unfold program_expression_progress;intros p globals Gamma Sigma vm m objects cells packets ef ty Hprogram.
   destruct Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent]. right.
   inversion Htyped;subst;split_children.
   all: try solve [first [eapply coherent_reference_progress_from_operand
         |eapply coherent_dereference_progress_from_operand
         |eapply coherent_assignment_progress_from_operands
         |eapply coherent_unary_progress_from_operand
         |eapply coherent_binary_progress_from_operands
         |eapply coherent_cast_progress_from_operand
         |eapply coherent_arrayread_progress_from_operand];
   [exact Hconfig|primitive_child_progress]].

 - unfold program_expression_preservation;intros p globals Gamma Sigma vm m objects cells packets ef ty final vm' next Hprogram Hstep.
   pose proof Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
   eapply program_result_lift;[exact Hprogram|].
   inversion Htyped;subst;split_children.
   all: first [
solve [eapply coherent_reference_preservation_from_operand;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_dereference_preservation_from_operand;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_assignment_preservation_from_operands;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_unary_preservation_from_operand;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_binary_preservation_from_operands;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_cast_preservation_from_operand;[exact Hconfig|primitive_child_preservation|exact Hstep]]
   |solve [eapply coherent_arrayread_preservation_from_operand;[exact Hconfig|primitive_child_preservation|exact Hstep]]].

Qed.
Print Assumptions program_primitive_case.
