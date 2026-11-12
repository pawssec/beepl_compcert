(* Conditionals may have different branch effects. The declared branch budget
   bounds either selected continuation and is retained while the guard steps. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_auxlemmas BeePL_soundness_memory.
Require Import BeePL_runtime_locations BeePL_initialized_runtime BeePL_initialized_lists.
Require Import BeePL_initialized_control BeePL_coherent_configurations.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Theorem coherent_conditional_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b yes no ef ty final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty) ef ty ->
  ssem_expr ge p vm m (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty) final vm' e' ->
  final = m /\ vm' = vm /\ exists selected_effect,
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' selected_effect ty /\
    sub_effect selected_effect ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b yes no ef ty final vm' e' [Hconfig Hcoherent] Hstep.
  destruct (initialized_conditional_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfig Hstep) as [Hm [Hvm [selected [Hsub Hnext]]]].
  split; [exact Hm |]. split; [exact Hvm |]. exists selected.
  split; [split; assumption |exact Hsub].
Qed.

Theorem coherent_conditional_preservation_from_guard :
  forall ge Gamma Sigma vm m objects cells packets p guard yes no ef ty final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Cond guard yes no ty) ef ty ->
  (forall guard_effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets guard guard_effect (Vtype Tbool) ->
    forall nextM nextVm next,
      ssem_expr ge p vm m guard nextM nextVm next ->
      exists Sigma' objects' cells' packets' effect',
        initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
        coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' (Vtype Tbool) /\
        sub_effect effect' guard_effect = true) ->
  ssem_expr ge p vm m (Cond guard yes no ty) final vm' e' ->
  exists Sigma' objects' cells' packets' effect',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' e' effect' ty /\
    sub_effect effect' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p guard yes no ef ty final vm' e' Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [HguardLoc [HyesLoc HnoLoc]] [HguardFrames [HyesFrames HnoFrames]]] Hcoherent].
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [guard_effect [budget [yes_effect [no_effect
      [Heffect [Hguard [Hyes [Hno [HyesBound HnoBound]]]]]]]]]. subst ef.
  assert (HguardConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets guard guard_effect (Vtype Tbool))
    by (split; [constructor; assumption |assumption]).
  assert (HyesConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets yes yes_effect ty)
    by (constructor; assumption).
  assert (HnoConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets no no_effect ty)
    by (constructor; assumption).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr ge p vm m guard _ _ _ |- _ =>
      destruct (Hchild guard_effect HguardConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
    destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HyesConfig Hupdate Hheap') as [_ Hyes' HyesLoc' HyesFrames'].
    destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HnoConfig Hupdate Hheap') as [_ Hno' HnoLoc' HnoFrames'].
    destruct Hnew as [_ Hguard' HguardLoc' HguardFrames'].
    exists Sigma', objects', cells', packets', (effect' ++ budget). split; [exact Hupdate |]. split.
    + split; [constructor; simpl; auto |exact Hcoherent'].
      eapply ty_cond; eassumption.
    + apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
  - destruct (coherent_conditional_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hconfig Hstep) as [Hm [Hvm [effect' [Hnext Hsub]]]].
    exists Sigma, objects, cells, packets, effect'. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; assumption.
  - destruct (coherent_conditional_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hconfig Hstep) as [Hm [Hvm [effect' [Hnext Hsub]]]].
    exists Sigma, objects, cells, packets, effect'. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; assumption.
Qed.

Theorem coherent_conditional_progress_from_guard :
  forall ge Gamma Sigma vm m objects cells packets p guard yes no ef ty,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Cond guard yes no ty) ef ty ->
  (forall guard_effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets guard guard_effect (Vtype Tbool) ->
    (exists v annotation, guard = Val v annotation) \/
      exists final vm' next, ssem_expr ge p vm m guard final vm' next) ->
  exists final vm' next, ssem_expr ge p vm m (Cond guard yes no ty) final vm' next.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p guard yes no ef ty
    [[Hheap Htyped [HguardLoc [HyesLoc HnoLoc]] [HguardFrames [HyesFrames HnoFrames]]] Hcoherent] Hchild.
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [guard_effect [budget [yes_effect [no_effect
      [Heffect [Hguard [Hyes [Hno [HyesBound HnoBound]]]]]]]]].
  eapply conditional_progress_from_guard; [exact Htyped |].
  apply (Hchild guard_effect). split; [constructor; assumption |exact Hcoherent].
Qed.

Print Assumptions coherent_conditional_head_preservation.
Print Assumptions coherent_conditional_preservation_from_guard.
Print Assumptions coherent_conditional_progress_from_guard.
