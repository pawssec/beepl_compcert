(* Casts retain the initialized coherent heap and decode values according to
   their target type. Context cases consume the recursive operand hypothesis. *)
Require Import List Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_proofs BeePL_soundness_memory.
Require Import BeePL_runtime_locations BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_operators BeePL_cast_soundness.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Lemma cast_typing_components : forall cenv Gamma Sigma operand target ef,
  type_expr cenv Gamma Sigma (Prim (Cast (Vtype target)) [operand] (Vtype target)) ef (Vtype target) ->
  exists source,
    type_expr cenv Gamma Sigma operand ef (Vtype source) /\
    allowed_cast source target = OK target.
Proof. intros; inversion H; subst; eauto. Qed.

Theorem coherent_cast_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p v annotation target ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Cast (Vtype target)) [Val v annotation] (Vtype target)) ef (Vtype target) ->
  ssem_expr ge p vm m (Prim (Cast (Vtype target)) [Val v annotation] (Vtype target)) final vm' e' ->
  final = m /\ vm' = vm /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil (Vtype target).
Proof.
  intros ge Gamma Sigma vm m objects cells packets p v annotation target ef final vm' e'
    [[Hheap Htyped Hloc Hframes] Hcoherent] Hstep.
  destruct (cast_typing_components _ _ _ _ _ _ Htyped) as [source [Hoperand Hallowed]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation.
  cbn [typeof_expr] in Hannotation. subst annotation.
  destruct (primitive_cast_value_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ Hoperand Hallowed Hstep)
    as [Hm [Hvm [result [He Hresult]]]]. subst final vm' e'.
  split; [reflexivity |]. split; [reflexivity |].
  apply primitive_value_configuration; assumption.
Qed.

Theorem coherent_cast_progress_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p operand target ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Cast (Vtype target)) [operand] (Vtype target)) ef (Vtype target) ->
  (forall source,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Vtype source) ->
    (exists v annotation, operand = Val v annotation) \/
      exists final vm' next, ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next,
    ssem_expr ge p vm m (Prim (Cast (Vtype target)) [operand] (Vtype target)) final vm' next.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p operand target ef
    [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent] Hchild.
  destruct (cast_typing_components _ _ _ _ _ _ Htyped) as [source [Hoperand Hallowed]].
  assert (Hconfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Vtype source))
    by (split; [constructor; assumption |exact Hcoherent]).
  destruct (Hchild source Hconfig) as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst operand. pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation.
    cbn [typeof_expr] in Hannotation. subst annotation.
    destruct (primitive_cast_value_progress ge p vm m _ _ _ _ _ _ Hoperand Hallowed)
      as [result [Hstep Hresult]]. eauto.
  - do 3 eexists. apply ssem_cast1. exact Hstep.
Qed.

Theorem coherent_cast_preservation_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p operand target ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Cast (Vtype target)) [operand] (Vtype target)) ef (Vtype target) ->
  (forall source,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Vtype source) ->
    forall nextM nextVm next,
      ssem_expr ge p vm m operand nextM nextVm next ->
      exists Sigma' objects' cells' packets' effect',
        initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
        coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' (Vtype source) /\
        sub_effect effect' ef = true) ->
  ssem_expr ge p vm m (Prim (Cast (Vtype target)) [operand] (Vtype target)) final vm' e' ->
  exists Sigma' objects' cells' packets' effect',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' e' effect' (Vtype target) /\
    sub_effect effect' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p operand target ef final vm' e' Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent].
  destruct (cast_typing_components _ _ _ _ _ _ Htyped) as [source [Hoperand Hallowed]].
  assert (HoperandConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Vtype source))
    by (split; [constructor; assumption |exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr ge p vm m operand _ _ _ |- _ =>
      destruct (Hchild source HoperandConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    destruct Hnew as [Hheap' Htyped' Hloc' Hframes'].
    exists Sigma', objects', cells', packets', effect'. split; [exact Hupdate |]. split; [|exact Hsub].
    split; [constructor; simpl; auto |exact Hcoherent']. eapply ty_cast; eassumption.
  - destruct (coherent_cast_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [Hm [Hvm Hresult]].
    exists Sigma, objects, cells, packets, nil. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [exact Hresult | apply sub_effect_nil].
Qed.

Print Assumptions coherent_cast_head_preservation.
Print Assumptions coherent_cast_progress_from_operand.
Print Assumptions coherent_cast_preservation_from_operand.
