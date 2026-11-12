(* Every actual successor agrees with the constructed scalar initializer;
   preservation is not restricted to a chosen evaluation derivation. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_packet_heap BeePL_packet_bindings.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_scalar_structure_heap BeePL_structure_initializer_determinism.
Import ListNotations.

Theorem evaluated_scalar_structure_preservation : forall p Gamma Sigma vm m objects cells packets sid attr ids es result ef final vm' e',
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets(Sinit sid ids es result) ef result ->
 structure_result_type sid attr result ->
 Forall(fun e=>exists v ty,e=Val v ty) es ->
 Forall(fun e=>is_aggregate_type(typeof_expr e)=false /\ typeof_expr e<>Bytes) es ->
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) final vm' e' ->
 exists fresh Sigma' objects' after,
 vm'=vm /\ e'=Val(Vloc fresh Ptrofs.zero) result /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' after packets /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm' final objects' after packets e' nil result.
Proof.
 intros * Hconfig Hshape Hvalues Hscalar Hstep.
 destruct(evaluated_scalar_structure_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hshape Hvalues Hscalar)
 as [expected [fresh [Sigma' [objects' [after [Hconstructed [Hevolution Hfinal]]]]]]].
 destruct(evaluated_structure_step_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hconstructed Hstep)
 as [Hm [Hvm He]]. subst final vm' e'.
 exists fresh,Sigma',objects',after. split;[reflexivity|]. split;[reflexivity|]. split;assumption.
Qed.

Print Assumptions evaluated_scalar_structure_preservation.
