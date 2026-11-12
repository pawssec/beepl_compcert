(* Recursive memory-expression contexts consume the child's preservation
   result and reframe suspended operands in the same evolved heap. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Import ListNotations.

Lemma memory_operand_type_unique : forall env Gamma Sigma e ef ty ef' ty',
  type_expr env Gamma Sigma e ef ty -> type_expr env Gamma Sigma e ef' ty' -> ty = ty'.
Proof.
  intros * Hfirst Hsecond.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hfirst).
  pose proof (type_rel_typeof _ _ _ _ _ _ Hsecond). congruence.
Qed.

Lemma typed_dereference_pointer_guards : forall env Gamma Sigma operand pt ef whole,
  type_expr env Gamma Sigma operand ef (Ptrtype pt) ->
  type_expr env Gamma Sigma (Prim Deref [operand] (get_data_type pt)) whole (get_data_type pt) ->
  is_option_ptr_type pt = false /\ type_is_volatile (transBeePL_type (get_data_type pt)) = false.
Proof.
  intros * Hoperand Hwhole. inversion Hwhole; subst.
  match goal with Hother : type_expr _ _ _ operand _ (Ptrtype ?other) |- _ =>
    assert (Heq : Ptrtype pt = Ptrtype other) by (eapply memory_operand_type_unique; eauto);
    inversion Heq; subst end.
  split; assumption.
Qed.

Lemma typed_assignment_pointer_guards : forall env Gamma Sigma left right pt ef whole,
  type_expr env Gamma Sigma left ef (Ptrtype pt) ->
  type_expr env Gamma Sigma (Prim Massgn [left; right] Utype) whole Utype ->
  is_option_ptr_type pt = false /\ type_is_volatile (transBeePL_type (get_data_type pt)) = false.
Proof.
  intros * Hoperand Hwhole. inversion Hwhole; subst.
  match goal with Hother : type_expr _ _ _ left _ (Ptrtype ?other) |- _ =>
    assert (Heq : Ptrtype pt = Ptrtype other) by (eapply memory_operand_type_unique; eauto);
    inversion Heq; subst end.
  split; assumption.
Qed.

Theorem coherent_reference_operand_context :
  forall ge Gamma Sigma vm m objects cells packets p operand basic attr ef
    Sigma' vm' m' objects' cells' packets' operand' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [operand] (Ptrtype (Reftype basic attr))) (ef ++ [Alloc]) (Ptrtype (Reftype basic attr)) ->
  ssem_expr ge p vm m operand m' vm' operand' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    operand' ef' (construct_type_btype basic) ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Prim Ref [operand] (Ptrtype (Reftype basic attr)))
    m' vm' (Prim Ref [operand'] (Ptrtype (Reftype basic attr))) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Prim Ref [operand'] (Ptrtype (Reftype basic attr))) (ef' ++ [Alloc]) (Ptrtype (Reftype basic attr)) /\
  sub_effect (ef' ++ [Alloc]) (ef ++ [Alloc]) = true.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hstep Hevolve
    [[Hheap' Hoperand' Hloc' Hframes'] Hcoherent'] Hsub.
  split; [apply ssem_ref1; exact Hstep |]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto.
    inversion Htyped; subst. eapply ty_ref; eauto.
  - apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
Qed.

Theorem coherent_dereference_operand_context :
  forall ge Gamma Sigma vm m objects cells packets p operand pt ef
    Sigma' vm' m' objects' cells' packets' operand' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [operand] (get_data_type pt)) (ef ++ [Read]) (get_data_type pt) ->
  type_expr ge.(genv_cenv) Gamma Sigma operand ef (Ptrtype pt) ->
  ssem_expr ge p vm m operand m' vm' operand' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    operand' ef' (Ptrtype pt) ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Prim Deref [operand] (get_data_type pt))
    m' vm' (Prim Deref [operand'] (get_data_type pt)) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Prim Deref [operand'] (get_data_type pt)) (ef' ++ [Read]) (get_data_type pt) /\
  sub_effect (ef' ++ [Read]) (ef ++ [Read]) = true.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hoperand Hstep Hevolve
    [[Hheap' Hoperand' Hloc' Hframes'] Hcoherent'] Hsub.
  destruct (typed_dereference_pointer_guards _ _ _ _ _ _ _ Hoperand Htyped) as [Hoption Hvolatile].
  split; [apply ssem_deref1; exact Hstep |]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto. eapply ty_deref; eauto.
  - apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
Qed.

Theorem coherent_field_operand_context :
  forall ge Gamma Sigma vm m objects cells packets p operand receiver field result ef
    Sigma' vm' m' objects' cells' packets' operand' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Sfield operand field result) ef result ->
  type_expr ge.(genv_cenv) Gamma Sigma operand ef receiver ->
  ssem_expr ge p vm m operand m' vm' operand' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' operand' ef' receiver ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Sfield operand field result) m' vm' (Sfield operand' field result) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Sfield operand' field result) ef' result /\ sub_effect ef' ef = true.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hoperand Hstep Hevolve
    [[Hheap' Hoperand' Hloc' Hframes'] Hcoherent'] Hsub.
  split; [apply ssem_sfield1; exact Hstep |]. split; [|exact Hsub].
  split; [|exact Hcoherent']. constructor; simpl; auto.
  inversion Htyped; subst.
  match goal with Hother : type_expr _ _ _ operand _ ?other |- _ =>
    assert (Heq : other = receiver) by (eapply memory_operand_type_unique; eauto);
    subst other end.
  eapply ty_sfield; eauto.
Qed.

Theorem coherent_assignment_left_context :
  forall ge Gamma Sigma vm m objects cells packets p left right pt ef1 ef2
    Sigma' vm' m' objects' cells' packets' left' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [left; right] Utype) (ef1 ++ ef2 ++ [Write]) Utype ->
  type_expr ge.(genv_cenv) Gamma Sigma left ef1 (Ptrtype pt) ->
  type_expr ge.(genv_cenv) Gamma Sigma right ef2 (get_data_type pt) ->
  ssem_expr ge p vm m left m' vm' left' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' left' ef' (Ptrtype pt) ->
  sub_effect ef' ef1 = true ->
  ssem_expr ge p vm m (Prim Massgn [left; right] Utype) m' vm' (Prim Massgn [left'; right] Utype) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Prim Massgn [left'; right] Utype) (ef' ++ ef2 ++ [Write]) Utype /\
  sub_effect (ef' ++ ef2 ++ [Write]) (ef1 ++ ef2 ++ [Write]) = true.
Proof.
  intros * [[Hheap Htyped [HleftLoc [HrightLoc Hnil]] [HleftFrames [HrightFrames HnilFrames]]] Hcoherent]
    Hleft Hright Hstep Hevolve [[Hheap' Hleft' HleftLoc' HleftFrames'] Hcoherent'] Hsub.
  destruct (typed_assignment_pointer_guards _ _ _ _ _ _ _ _ Hleft Htyped) as [Hoption Hvolatile].
  assert (HrightConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    right ef2 (get_data_type pt)) by (constructor; assumption).
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HrightConfig Hevolve Hheap') as [_ Hright' HrightLoc' HrightFrames'].
  split; [apply ssem_massgn1; exact Hstep |]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto. eapply ty_massgn; eauto.
  - apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
Qed.

Theorem coherent_assignment_right_context :
  forall ge Gamma Sigma vm m objects cells packets p b offset right pt ef
    Sigma' vm' m' objects' cells' packets' right' ef',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b offset) (Ptrtype pt); right] Utype) (ef ++ [Write]) Utype ->
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc b offset) (Ptrtype pt)) [] (Ptrtype pt) ->
  ssem_expr ge p vm m right m' vm' right' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' right' ef' (get_data_type pt) ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Prim Massgn [Val (Vloc b offset) (Ptrtype pt); right] Utype)
    m' vm' (Prim Massgn [Val (Vloc b offset) (Ptrtype pt); right'] Utype) /\
  coherent_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (Prim Massgn [Val (Vloc b offset) (Ptrtype pt); right'] Utype) (ef' ++ [Write]) Utype /\
  sub_effect (ef' ++ [Write]) (ef ++ [Write]) = true.
Proof.
  intros * [[Hheap Htyped [HleftLoc [HrightLoc Hnil]] [HleftFrames [HrightFrames HnilFrames]]] Hcoherent]
    Hleft Hstep Hevolve [[Hheap' Hright' HrightLoc' HrightFrames'] Hcoherent'] Hsub.
  destruct (typed_assignment_pointer_guards _ _ _ _ _ _ _ _ Hleft Htyped) as [Hoption Hvolatile].
  assert (HleftConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Val (Vloc b offset) (Ptrtype pt)) [] (Ptrtype pt)) by (constructor; assumption).
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HleftConfig Hevolve Hheap') as [_ Hleft' HleftLoc' HleftFrames'].
  split; [apply ssem_massgn2; exact Hstep |]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto.
    change (ef' ++ [Write]) with ([] ++ ef' ++ [Write]). eapply ty_massgn; eauto.
  - apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
Qed.

Print Assumptions coherent_reference_operand_context.
Print Assumptions coherent_dereference_operand_context.
Print Assumptions coherent_field_operand_context.
Print Assumptions coherent_assignment_left_context.
Print Assumptions coherent_assignment_right_context.
