(* Finite executions of the actual source small-step semantics.  These results
   use the discharged whole-expression theorem, not a soundness hypothesis.
   They preserve source types/effect budgets and the complete shared heap;
   they do not assert termination or adequacy of an external initial state. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas BeePL_substitution_proofs.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_program_soundness_assembly.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations BeePL_coherent_lists.
Import ListNotations.

Definition program_list_configuration p globals Gamma Sigma vm m objects cells packets es ef ts : Prop :=
 program_runtime_invariant(globalenv p) globals Sigma objects cells packets /\
 coherent_list_configuration(globalenv p) Gamma Sigma vm m objects cells packets es ef ts.

Lemma program_list_step_preservation :
 forall p globals Gamma Sigma vm m objects cells packets es ef ts final vm' next,
 program_list_configuration p globals Gamma Sigma vm m objects cells packets es ef ts ->
 ssem_exprs(globalenv p) p vm m es final vm' next ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_list_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' ts /\
 sub_effect ef' ef=true.
Proof.
 intros * [Hprogram Hconfig] Hstep.
 assert(Hsafe:Forall program_expression_safe es).
 { apply Forall_forall;intros;apply program_expression_soundness. }
 destruct(program_list_preservation es Hsafe p globals Gamma Sigma vm m objects cells packets ef ts final vm' next Hprogram Hconfig Hstep)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnew Hsub]]]]]]].
 exists Sigma',objects',cells',packets',ef';split;[exact Hevolve|]. split;[|exact Hsub].
 split;[eapply program_runtime_invariant_evolve;eauto|exact Hnew].
Qed.

Theorem program_closure_preservation :
 forall ge p vm m e n final vm' next,
 ssem_closure ge p vm m e n final vm' next -> ge=globalenv p ->
 forall globals Gamma Sigma objects cells packets ef ty,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_runtime_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true.
Proof.
 intros ge p vm m e n final vm' next Hclosure.
 induction Hclosure;intros Henv globals Gamma Sigma objects cells packets ef ty Hconfig;subst bge.
 - exists Sigma,objects,cells,packets,ef;split.
   + destruct Hconfig as [Hcode [[Hheap Htyped Hloc Hframes] Hcoherent]].
     eapply initialized_heap_evolution_refl;exact Hheap.
   + split;[exact Hconfig|apply sub_effect_refl].
 - eapply program_expression_preservation_checked;eassumption.
 - destruct(program_expression_preservation_checked e p globals Gamma Sigma vm m objects cells packets ef ty m' vm' e' Hconfig H)
   as [Sigma1 [objects1 [cells1 [packets1 [ef1 [Hfirst [Hmiddle Hsub1]]]]]]].
   destruct(IHHclosure eq_refl globals Gamma Sigma1 objects1 cells1 packets1 ef1 ty Hmiddle)
   as [Sigma2 [objects2 [cells2 [packets2 [ef2 [Hrest [Hlast Hsub2]]]]]]].
   exists Sigma2,objects2,cells2,packets2,ef2;split.
   + eapply initialized_heap_evolution_trans;eassumption.
   + split;[exact Hlast|eapply sub_effect_trans;eassumption].
Qed.

Theorem program_closures_preservation :
 forall ge p vm m es n final vm' next,
 ssem_closures ge p vm m es n final vm' next -> ge=globalenv p ->
 forall globals Gamma Sigma objects cells packets ef ts,
 program_list_configuration p globals Gamma Sigma vm m objects cells packets es ef ts ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_list_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' ts /\
 sub_effect ef' ef=true.
Proof.
 intros ge p vm m es n final vm' next Hclosure.
 induction Hclosure;intros Henv globals Gamma Sigma objects cells packets ef ts Hconfig;subst bge.
 - eapply program_list_step_preservation;eassumption.
 - destruct(program_list_step_preservation p globals Gamma Sigma vm m objects cells packets e ef ts m' vm' e' Hconfig H)
   as [Sigma1 [objects1 [cells1 [packets1 [ef1 [Hfirst [Hmiddle Hsub1]]]]]]].
   destruct(IHHclosure eq_refl globals Gamma Sigma1 objects1 cells1 packets1 ef1 ts Hmiddle)
   as [Sigma2 [objects2 [cells2 [packets2 [ef2 [Hrest [Hlast Hsub2]]]]]]].
   exists Sigma2,objects2,cells2,packets2,ef2;split.
   + eapply initialized_heap_evolution_trans;eassumption.
   + split;[exact Hlast|eapply sub_effect_trans;eassumption].
Qed.

Theorem program_closure_cannot_get_stuck :
 forall p globals Gamma Sigma vm m objects cells packets e ef ty n final vm' next,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 ssem_closure(globalenv p) p vm m e n final vm' next ->
 (exists v annotation,next=Val v annotation) \/
 exists final' vm'' next',ssem_expr(globalenv p) p vm' final next final' vm'' next'.
Proof.
 intros * Hconfig Hclosure.
 destruct(program_closure_preservation _ _ _ _ _ _ _ _ _ Hclosure eq_refl _ _ _ _ _ _ _ _ Hconfig)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnext Hsub]]]]]]].
 eapply program_expression_progress_checked;exact Hnext.
Qed.

(* Conventional reflexive reachability also includes zero steps from a
   nonvalue expression. The original ssem_closure is retained above. *)
Inductive program_reaches (p : program) : vmap -> Mem.mem -> expr -> vmap -> Mem.mem -> expr -> Prop :=
| program_reaches_refl : forall vm m e, program_reaches p vm m e vm m e
| program_reaches_step : forall vm m e vm1 m1 e1 vm2 m2 e2,
 ssem_expr(globalenv p) p vm m e m1 vm1 e1 ->
 program_reaches p vm1 m1 e1 vm2 m2 e2 ->
 program_reaches p vm m e vm2 m2 e2.

Theorem program_reaches_preservation :
 forall p vm m e finalVm final next,
 program_reaches p vm m e finalVm final next ->
 forall globals Gamma Sigma objects cells packets ef ty,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 exists Sigma' objects' cells' packets' ef',
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_runtime_configuration p globals Gamma Sigma' finalVm final objects' cells' packets' next ef' ty /\
 sub_effect ef' ef=true.
Proof.
 intros p vm m e finalVm final next Hreach.
 induction Hreach;intros globals Gamma Sigma objects cells packets ef ty Hconfig.
 - exists Sigma,objects,cells,packets,ef;split.
   + destruct Hconfig as [Hcode [[Hheap Htyped Hloc Hframes] Hcoherent]].
     eapply initialized_heap_evolution_refl;exact Hheap.
   + split;[exact Hconfig|apply sub_effect_refl].
 - destruct(program_expression_preservation_checked e p globals Gamma Sigma vm m objects cells packets ef ty m1 vm1 e1 Hconfig H)
   as [Sigma1 [objects1 [cells1 [packets1 [ef1 [Hfirst [Hmiddle Hsub1]]]]]]].
   destruct(IHHreach globals Gamma Sigma1 objects1 cells1 packets1 ef1 ty Hmiddle)
   as [Sigma2 [objects2 [cells2 [packets2 [ef2 [Hrest [Hlast Hsub2]]]]]]].
   exists Sigma2,objects2,cells2,packets2,ef2;split.
   + eapply initialized_heap_evolution_trans;eassumption.
   + split;[exact Hlast|eapply sub_effect_trans;eassumption].
Qed.

Theorem program_reaches_cannot_get_stuck :
 forall p globals Gamma Sigma vm m objects cells packets e ef ty finalVm final next,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 program_reaches p vm m e finalVm final next ->
 (exists v annotation,next=Val v annotation) \/
 exists final' vm'' next',ssem_expr(globalenv p) p finalVm final next final' vm'' next'.
Proof.
 intros * Hconfig Hreach.
 destruct(program_reaches_preservation _ _ _ _ _ _ _ Hreach _ _ _ _ _ _ _ _ Hconfig)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnext Hsub]]]]]]].
 eapply program_expression_progress_checked;exact Hnext.
Qed.

Print Assumptions program_closure_preservation.
Print Assumptions program_closures_preservation.
Print Assumptions program_reaches_cannot_get_stuck.

(* The paper's terminal-state result is a normal-form theorem, not a
   termination theorem. Allocation is reflected by the extended Sigma'. *)
Theorem program_closure_normal_form_is_typed_value :
 forall p globals Gamma Sigma vm m objects cells packets e ef ty n final vm' next,
 program_runtime_configuration p globals Gamma Sigma vm m objects cells packets e ef ty ->
 ssem_closure(globalenv p) p vm m e n final vm' next ->
 (forall nextM nextVm nextExpr,~ssem_expr(globalenv p) p vm' final next nextM nextVm nextExpr) ->
 exists v Sigma' objects' cells' packets',
 next=Val v ty /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
 program_runtime_configuration p globals Gamma Sigma' vm' final objects' cells' packets'(Val v ty) [] ty /\
 sub_effect [] ef=true.
Proof.
 intros * Hconfig Hclosure Hnormal.
 destruct(program_closure_preservation _ _ _ _ _ _ _ _ _ Hclosure eq_refl _ _ _ _ _ _ _ _ Hconfig)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnext Hsub]]]]]]].
 destruct(program_expression_progress_checked next p globals Gamma Sigma' vm' final objects' cells' packets' ef' ty Hnext)
 as [[v [annotation Heq]]|[nextM [nextVm [nextExpr Hstep]]]].
 - subst next. pose proof Hnext as [Hcode [[Hheap Htyped Hloc Hframes] Hcoherent]].
   pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hannotation;simpl in Hannotation;subst annotation.
   pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Htyped) as Hnil;subst ef'.
   exists v,Sigma',objects',cells',packets';split;[reflexivity|]. split;[exact Hevolve|]. split;[exact Hnext|exact Hsub].
 - exfalso;exact(Hnormal _ _ _ Hstep).
Qed.

(* List semantics contains an identity summary for lists of values. Therefore
   its useful progress statement distinguishes values from nonvalue lists,
   rather than using an impossible no-step normal form for a value list. *)
Theorem program_closures_values_or_progress :
 forall p globals Gamma Sigma vm m objects cells packets es ef ts n final vm' next,
 program_list_configuration p globals Gamma Sigma vm m objects cells packets es ef ts ->
 ssem_closures(globalenv p) p vm m es n final vm' next ->
 is_values next=true \/
 (is_values next=false /\ exists nextM nextVm nextExprs,
 ssem_exprs(globalenv p) p vm' final next nextM nextVm nextExprs).
Proof.
 intros * Hconfig Hclosure.
 destruct(is_values next) eqn:Hvalues;[left;reflexivity|right;split;[reflexivity|]].
 destruct(program_closures_preservation _ _ _ _ _ _ _ _ _ Hclosure eq_refl _ _ _ _ _ _ _ _ Hconfig)
 as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [[Hprogram Hnext] Hsub]]]]]]].
 eapply program_list_progress;[|exact Hprogram|exact Hnext].
 apply Forall_forall;intros;apply program_expression_soundness.
Qed.
Print Assumptions program_closure_normal_form_is_typed_value.
Print Assumptions program_closures_values_or_progress.
