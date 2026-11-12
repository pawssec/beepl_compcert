(* Induction interfaces for the whole expression theorem.  These are proof
   properties, not a restriction on the BeePL syntax or a runtime oracle. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_initialized_runtime BeePL_initialized_lists.
Require Import BeePL_coherent_configurations BeePL_coherent_lists.
Import ListNotations.

Definition program_expression_progress (e : expr) : Prop :=
 forall p globals Gamma Sigma vm m objects cells packets ef ty,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 (exists v annotation,e=Val v annotation) \/
 exists final vm' next,ssem_expr(globalenv p) p vm m e final vm' next.

Definition program_expression_preservation (e : expr) : Prop :=
 forall p globals Gamma Sigma vm m objects cells packets ef ty final vm' next,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 ssem_expr(globalenv p) p vm m e final vm' next ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_runtime_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true.

Definition program_expression_safe e :=
 program_expression_progress e /\ program_expression_preservation e.

Lemma program_list_progress : forall es,
 Forall program_expression_safe es ->
 forall p globals Gamma Sigma vm m objects cells packets ef ts,
 program_runtime_invariant(globalenv p) globals Sigma objects cells packets ->
 coherent_list_configuration(globalenv p) Gamma Sigma vm m objects cells packets es ef ts ->
 exists final vm' next,ssem_exprs(globalenv p) p vm m es final vm' next.
Proof.
 intros es Hchildren * Hprogram Hconfig.
 eapply coherent_list_progress_from_expressions;[exact Hconfig|].
 intros e Hin effect ty Hchild.
 destruct(proj1(Forall_forall _ _) Hchildren e Hin) as [Hprogress Hpreserve].
 apply (Hprogress p globals Gamma Sigma vm m objects cells packets effect ty). constructor;assumption.
Qed.

Lemma program_list_preservation : forall es,
 Forall program_expression_safe es ->
 forall p globals Gamma Sigma vm m objects cells packets ef ts final vm' next,
 program_runtime_invariant(globalenv p) globals Sigma objects cells packets ->
 coherent_list_configuration(globalenv p) Gamma Sigma vm m objects cells packets es ef ts ->
 ssem_exprs(globalenv p) p vm m es final vm' next ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 coherent_list_configuration(globalenv p) Gamma Sigma' vm' final objects' cells' packets' next ef' ts /\
 sub_effect ef' ef=true.
Proof.
 intros es Hchildren * Hprogram Hconfig Hstep.
 eapply coherent_list_preservation_from_expressions;[exact Hconfig| |exact Hstep].
 intros e Hin effect ty Hchild nextM nextVm child HchildStep.
 destruct(proj1(Forall_forall _ _) Hchildren e Hin) as [Hprogress Hpreserve].
 assert(HchildConfig:program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e effect ty) by (constructor;assumption).
 destruct(Hpreserve p globals Gamma Sigma vm m objects cells packets effect ty nextM nextVm child
 HchildConfig HchildStep)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnew Hsub]]]]]]].
 exists Sigma',objects',cells',packets',ef';split;[exact Hevolve|].
 split;[destruct Hnew;assumption|exact Hsub].
Qed.

Lemma program_child_progress : forall e,
 program_expression_safe e ->
 forall p globals Gamma Sigma vm m objects cells packets ef ty,
 program_runtime_invariant(globalenv p) globals Sigma objects cells packets ->
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets e ef ty ->
 (exists v annotation,e=Val v annotation) \/
 exists final vm' next,ssem_expr(globalenv p) p vm m e final vm' next.
Proof. intros e [Hprogress Hpreserve] * Hcode Hconfig. eapply Hprogress;constructor;eassumption. Qed.

Lemma program_child_preservation : forall e,
 program_expression_safe e ->
 forall p globals Gamma Sigma vm m objects cells packets ef ty final vm' next,
 program_runtime_invariant(globalenv p) globals Sigma objects cells packets ->
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets e ef ty ->
 ssem_expr(globalenv p) p vm m e final vm' next ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true.
Proof.
 intros e [Hprogress Hpreserve] * Hcode Hconfig Hstep.
 assert(Hprogram:program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty) by (constructor;assumption).
 destruct(Hpreserve _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram Hstep)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnew Hsub]]]]]]].
 exists Sigma',objects',cells',packets',ef';split;[exact Hevolve|]. split;[destruct Hnew;assumption|exact Hsub].
Qed.

Lemma program_result_lift :
 forall p globals Gamma Sigma vm m objects cells packets e ef ty final vm' next,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 (exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true) ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_runtime_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true.
Proof.
 intros * Hprogram [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnew Hsub]]]]]]].
 exists Sigma',objects',cells',packets',ef';split;[exact Hevolve|]. split;[|exact Hsub].
 eapply program_runtime_configuration_after_step;eauto.
Qed.
