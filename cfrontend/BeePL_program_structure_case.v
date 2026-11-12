(* Full Sinit constructor for the expression induction: recursive argument
   evaluation, followed by the checked heterogeneous initializer head. *)
Require Import List Bool Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_initialized_runtime.
Require Import BeePL_initialized_lists BeePL_coherent_lists BeePL_initialized_contexts.
Require Import BeePL_coherent_configurations BeePL_mixed_structure_configurations.
Require Import BeePL_strict_progress BeePL_substitution_proofs BeePL_auxlemmas.
Import ListNotations.

Lemma structure_list_configuration : forall ge Gamma Sigma vm m objects cells packets sid ids es rt ef,
 coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(Sinit sid ids es rt) ef rt ->
 exists ts,coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts.
Proof.
 intros * [[Hheap Htyped Hloc Hframes] Hcoherent].
 inversion Htyped;subst. eexists;split;[constructor;eassumption|exact Hcoherent].
Qed.

Theorem program_structure_case : forall sid ids es rt,
 Forall program_expression_safe es -> program_expression_safe(Sinit sid ids es rt).
Proof.
 intros sid ids es rt Hchildren. split.
 - unfold program_expression_progress. intros p globals Gamma Sigma vm m objects cells packets ef ty Hprogram.
   pose proof Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
   pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hann;simpl in Hann;subst ty. right.
   destruct(is_values es) eqn:Hvalues.
   + apply is_values_all_value_arguments in Hvalues.
     destruct(evaluated_structure_configuration_progress _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hvalues)
       as [final [fresh [Sigma' [objects' [cells' [packets' [Hstep Hrest]]]]]]]. do 3 eexists;exact Hstep.
   + destruct(structure_list_configuration _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig) as [ts Hargs].
     destruct(program_list_progress es Hchildren p globals Gamma Sigma vm m objects cells packets ef ts Hcode Hargs)
       as [final [vm' [next Hstep]]]. exists final,vm',(Sinit sid ids next rt). apply ssem_sinit1;assumption.
 - unfold program_expression_preservation. intros p globals Gamma Sigma vm m objects cells packets ef ty final vm' next Hprogram Hstep.
   pose proof Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
   pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hann;simpl in Hann;subst ty.
   eapply program_result_lift;[exact Hprogram|].
   inversion Hstep;subst.
   + destruct(structure_list_configuration _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig) as [ts Hargs].
     destruct(program_list_preservation es Hchildren p globals Gamma Sigma vm m objects cells packets ef ts final vm' es' Hcode Hargs H10)
       as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [[Hargs' Hcoherent'] Hsub]]]]]]].
     destruct(initialized_structure_arguments_context (globalenv p) Gamma Sigma vm m objects cells packets p sid ids es rt ef ts
         Sigma' vm' final objects' cells' packets' es' ef'
         (proj1 Hconfig) (initialized_list_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hargs))
         H9 H10 Hevolve Hargs' Hsub) as [_ [Hnew HsubFinal]].
     exists Sigma',objects',cells',packets',ef';split;[exact Hevolve|]. split;[split;assumption|exact HsubFinal].
   + destruct(evaluated_structure_configuration_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig ltac:(assumption) Hstep)
       as [fresh [Sigma' [objects' [cells' [packets' [Hvm [Heq [Hevolve Hnew]]]]]]]].
     exists Sigma',objects',cells',packets',[];split;[exact Hevolve|]. split;[exact Hnew|apply sub_effect_nil].
Qed.
Print Assumptions program_structure_case.
