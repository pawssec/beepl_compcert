(* Exhaustive reference-allocation heads over the existing basic types.
   Aggregate copy readiness comes from the coherent program heap. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs BeePL_auxlemmas.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_references BeePL_located_aggregate_reference.
Import ListNotations.

Lemma typed_aggregate_value_address : forall env Gamma Sigma v annotation ef ty,
  type_expr env Gamma Sigma (Val v annotation) ef ty ->
  is_aggregate_type ty = true -> exists b offset, v = Vloc b offset.
Proof.
  intros * Htyped Hkind.
  inversion Htyped; subst; simpl in Hkind; try discriminate; eauto.
Qed.

Lemma typed_reference_operand : forall env Gamma Sigma v annotation basic attr ef,
  type_expr env Gamma Sigma
    (Prim Ref [Val v annotation] (Ptrtype (Reftype basic attr))) ef (Ptrtype (Reftype basic attr)) ->
  annotation = construct_type_btype basic /\
  type_expr env Gamma Sigma (Val v annotation) [] (construct_type_btype basic).
Proof.
  intros * Htyped. inversion Htyped; subst.
  match goal with Hvalue : type_expr _ _ _ (Val _ _) _ _ |- _ =>
    pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
    pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Heffect;
    simpl in Hannotation; subst end.
  split; [reflexivity |assumption].
Qed.

Theorem coherent_general_reference_head_progress :
  forall p Gamma Sigma vm m objects cells packets v annotation basic attr ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [Val v annotation] (Ptrtype (Reftype basic attr))) ef (Ptrtype (Reftype basic attr)) ->
  exists final fresh Sigma' objects' cells' packets',
    ssem_expr (globalenv p) p vm m
      (Prim Ref [Val v annotation] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm final objects' cells' packets'
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) [] (Ptrtype (Reftype basic attr)).
Proof.
  intros * Hconfig.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (typed_reference_operand _ _ _ _ _ _ _ _ Htyped) as [Hannotation Hvalue]. subst annotation.
  destruct basic as [pt|sid sa|pt len sa].
  - destruct (coherent_primitive_reference_progress (globalenv p) Gamma Sigma vm m objects cells packets p pt attr v ef Hconfig)
      as [final [fresh [Hstep [Hevolve Hfinal]]]].
    exists final, fresh. do 4 eexists. split; [exact Hstep |]. split; [exact Hevolve |exact Hfinal].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hvalue eq_refl) as [b [offset Hv]]. subst v.
    eapply program_located_aggregate_reference_progress; [exact Hconfig |reflexivity].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hvalue eq_refl) as [b [offset Hv]]. subst v.
    eapply program_located_aggregate_reference_progress; [exact Hconfig |reflexivity].
Qed.

Theorem coherent_general_reference_head_preservation :
  forall p Gamma Sigma vm m objects cells packets v annotation basic attr ef final vm' next,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [Val v annotation] (Ptrtype (Reftype basic attr))) ef (Ptrtype (Reftype basic attr)) ->
  ssem_expr (globalenv p) p vm m
    (Prim Ref [Val v annotation] (Ptrtype (Reftype basic attr))) final vm' next ->
  exists Sigma' objects' cells' packets',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets'
      next [] (Ptrtype (Reftype basic attr)) /\ sub_effect [] ef = true.
Proof.
  intros * Hconfig Hstep.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (typed_reference_operand _ _ _ _ _ _ _ _ Htyped) as [Hannotation Hvalue]. subst annotation.
  destruct basic as [pt|sid sa|pt len sa].
  - destruct (coherent_primitive_reference_preservation (globalenv p) Gamma Sigma vm m objects cells packets p pt attr v ef final vm' next Hconfig Hstep)
      as [fresh [Hvm [He [Hevolve Hfinal]]]].
    do 4 eexists. split; [exact Hevolve |]. split; [exact Hfinal |apply sub_effect_nil].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hvalue eq_refl) as [b [offset Hv]]. subst v.
    destruct (program_located_aggregate_reference_preservation p Gamma Sigma vm m objects cells packets b offset (Bstruct sid sa) attr ef final vm' next Hconfig eq_refl Hstep)
      as [fresh [Sigma' [objects' [cells' [packets' [Hvm [He [Hevolve [Hfinal Hsub]]]]]]]]].
    exists Sigma', objects', cells', packets'. split; [exact Hevolve |]. split; assumption.
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hvalue eq_refl) as [b [offset Hv]]. subst v.
    destruct (program_located_aggregate_reference_preservation p Gamma Sigma vm m objects cells packets b offset (Barray pt len sa) attr ef final vm' next Hconfig eq_refl Hstep)
      as [fresh [Sigma' [objects' [cells' [packets' [Hvm [He [Hevolve [Hfinal Hsub]]]]]]]]].
    exists Sigma', objects', cells', packets'. split; [exact Hevolve |]. split; assumption.
Qed.

Print Assumptions coherent_general_reference_head_progress.
Print Assumptions coherent_general_reference_head_preservation.
