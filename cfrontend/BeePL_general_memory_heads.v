(* Exhaustive typed dereference and assignment heads. Optional pointers must
   first be matched; the remaining inhabited pointer values are references. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_soundness_memory.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_reads BeePL_coherent_aggregate_dereference.
Require Import BeePL_general_reference_heads BeePL_extent_copy_readiness.
Import ListNotations.

Lemma typed_nonoption_pointer_value : forall env Gamma Sigma v annotation ef pt,
  type_expr env Gamma Sigma (Val v annotation) ef (Ptrtype pt) ->
  is_option_ptr_type pt = false ->
  exists basic attr b offset,
    pt = Reftype basic attr /\ v = Vloc b offset /\ annotation = Ptrtype pt.
Proof. intros * Htyped Hoption; inversion Htyped; subst; try discriminate; eauto 10. Qed.

Lemma dereference_typing_components : forall env Gamma Sigma operand result ef,
  type_expr env Gamma Sigma (Prim Deref [operand] result) ef result ->
  exists pt child_effect,
    result = get_data_type pt /\ ef = child_effect ++ [Read] /\
    type_expr env Gamma Sigma operand child_effect (Ptrtype pt) /\ is_option_ptr_type pt = false.
Proof. intros * Htyped; inversion Htyped; subst; eauto 8. Qed.

Lemma assignment_typing_components : forall env Gamma Sigma left right ef,
  type_expr env Gamma Sigma (Prim Massgn [left; right] Utype) ef Utype ->
  exists pt left_effect right_effect,
    ef = left_effect ++ right_effect ++ [Write] /\
    type_expr env Gamma Sigma left left_effect (Ptrtype pt) /\
    type_expr env Gamma Sigma right right_effect (get_data_type pt) /\ is_option_ptr_type pt = false.
Proof. intros * Htyped; inversion Htyped; subst; eauto 9. Qed.

Theorem coherent_general_dereference_head_progress :
  forall ge Gamma Sigma vm m objects cells packets p v annotation result ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val v annotation] result) ef result ->
  exists value,
    ssem_expr ge p vm m (Prim Deref [Val v annotation] result) m vm (Val value result) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val value result) [] result.
Proof.
  intros * Hconfig. pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (dereference_typing_components _ _ _ _ _ _ Htyped)
    as [pt [effect [Hresult [Hef [Hvalue Hoption]]]]].
  destruct (typed_nonoption_pointer_value _ _ _ _ _ _ _ Hvalue Hoption)
    as [basic [attr [b [offset [Hpt [Hv Hannotation]]]]]]. subst pt v annotation result.
  destruct basic as [primitive|sid sa|primitive len sa].
  - destruct (coherent_primitive_deref_progress ge Gamma Sigma vm m objects cells packets p b offset primitive attr ef Hconfig)
      as [value [Hstep Hfinal]].
    exists value. split; [exact Hstep |]. split; [|exact Hfinal].
    eapply initialized_heap_evolution_refl; exact Hheap.
  - exists (Vloc b offset). eapply coherent_aggregate_deref_progress; [exact Hconfig |reflexivity].
  - exists (Vloc b offset). eapply coherent_aggregate_deref_progress; [exact Hconfig |reflexivity].
Qed.

Theorem coherent_general_dereference_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p v annotation result ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val v annotation] result) ef result ->
  ssem_expr ge p vm m (Prim Deref [Val v annotation] result) final vm' next ->
  final = m /\ vm' = vm /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next [] result.
Proof.
  intros * Hconfig Hstep. pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (dereference_typing_components _ _ _ _ _ _ Htyped)
    as [pt [effect [Hresult [Hef [Hvalue Hoption]]]]].
  destruct (typed_nonoption_pointer_value _ _ _ _ _ _ _ Hvalue Hoption)
    as [basic [attr [b [offset [Hpt [Hv Hannotation]]]]]]. subst pt v annotation result.
  destruct basic as [primitive|sid sa|primitive len sa].
  - destruct (coherent_primitive_deref_preservation ge Gamma Sigma vm m objects cells packets p b offset primitive attr ef final vm' next Hconfig Hstep)
      as [Hm [Hvm Hfinal]]. subst final vm'.
    split; [reflexivity |]. split; [reflexivity |]. split; [|exact Hfinal].
    eapply initialized_heap_evolution_refl; exact Hheap.
  - exact (coherent_aggregate_deref_preservation ge Gamma Sigma vm m objects cells packets p b offset
      (Bstruct sid sa) attr ef final vm' next Hconfig eq_refl Hstep).
  - exact (coherent_aggregate_deref_preservation ge Gamma Sigma vm m objects cells packets p b offset
      (Barray primitive len sa) attr ef final vm' next Hconfig eq_refl Hstep).
Qed.

Theorem coherent_general_assignment_head_progress :
  forall p Gamma Sigma vm m objects cells packets left left_annotation right right_annotation ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val left left_annotation; Val right right_annotation] Utype) ef Utype ->
  exists final,
    ssem_expr (globalenv p) p vm m
      (Prim Massgn [Val left left_annotation; Val right right_annotation] Utype) final vm (Val Vunit Utype) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm final objects cells packets (Val Vunit Utype) [] Utype.
Proof.
  intros * Hconfig. pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (assignment_typing_components _ _ _ _ _ _ Htyped)
    as [pt [left_effect [right_effect [Hef [Hleft [Hright Hoption]]]]]].
  destruct (typed_nonoption_pointer_value _ _ _ _ _ _ _ Hleft Hoption)
    as [basic [attr [b [offset [Hpt [Hv Hannotation]]]]]]. subst pt left left_annotation.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as HrightAnnotation.
  simpl in HrightAnnotation. subst right_annotation.
  destruct basic as [primitive|sid sa|primitive len sa].
  - eapply coherent_primitive_assignment_progress; exact Hconfig.
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hright eq_refl) as [src [source Hv]]. subst right.
    eapply program_coherent_aggregate_assignment_progress; [exact Hconfig |reflexivity].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hright eq_refl) as [src [source Hv]]. subst right.
    eapply program_coherent_aggregate_assignment_progress; [exact Hconfig |reflexivity].
Qed.

Theorem coherent_general_assignment_head_preservation :
  forall p Gamma Sigma vm m objects cells packets left left_annotation right right_annotation ef final vm' next,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val left left_annotation; Val right right_annotation] Utype) ef Utype ->
  ssem_expr (globalenv p) p vm m
    (Prim Massgn [Val left left_annotation; Val right right_annotation] Utype) final vm' next ->
  vm' = vm /\ next = Val Vunit Utype /\
  initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm' final objects cells packets next [] Utype /\
  sub_effect [] ef = true.
Proof.
  intros * Hconfig Hstep. pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (assignment_typing_components _ _ _ _ _ _ Htyped)
    as [pt [left_effect [right_effect [Hef [Hleft [Hright Hoption]]]]]].
  destruct (typed_nonoption_pointer_value _ _ _ _ _ _ _ Hleft Hoption)
    as [basic [attr [b [offset [Hpt [Hv Hannotation]]]]]]. subst pt left left_annotation.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as HrightAnnotation.
  simpl in HrightAnnotation. subst right_annotation.
  destruct basic as [primitive|sid sa|primitive len sa].
  - eapply coherent_primitive_assignment_preservation; [exact Hconfig |exact Hstep].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hright eq_refl) as [src [source Hv]]. subst right.
    eapply program_coherent_aggregate_assignment_preservation; [exact Hconfig |reflexivity |exact Hstep].
  - destruct (typed_aggregate_value_address _ _ _ _ _ _ _ Hright eq_refl) as [src [source Hv]]. subst right.
    eapply program_coherent_aggregate_assignment_preservation; [exact Hconfig |reflexivity |exact Hstep].
Qed.

Print Assumptions coherent_general_dereference_head_progress.
Print Assumptions coherent_general_dereference_head_preservation.
Print Assumptions coherent_general_assignment_head_progress.
Print Assumptions coherent_general_assignment_head_preservation.
