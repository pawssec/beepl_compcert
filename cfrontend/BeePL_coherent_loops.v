(* Incremental loop execution.  Entry and iteration boundaries need no
   termination premise; active-body steps use the expression induction
   hypothesis while the template retains its typing and runtime locations. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_type_equality BeePL_substitution_proofs BeePL_auxlemmas.
Require Import BeePL_soundness_memory BeePL_loop_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Require Import BeePL_layout_coherence BeePL_soundness_store.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Lemma typed_loop_value_bounds : forall cenv Gamma Sigma first ta last tb d body ef,
  type_expr cenv Gamma Sigma (For (Val first ta) (Val last tb) d body Utype) ef Utype ->
  exists pt,
    ta = Vtype pt /\ tb = Vtype pt /\
    typeof_value first (Vtype pt) /\ typeof_value last (Vtype pt) /\
    (is_primint (Vtype pt) || is_primlong (Vtype pt))%bool = true /\
    type_expr cenv Gamma Sigma body ef Utype.
Proof.
  intros cenv Gamma Sigma first ta last tb d body ef Htyped.
  inversion Htyped; subst.
  match goal with
  | Hfirst : type_expr _ _ _ (Val first ta) ?e1 ?t1,
    Hlast : type_expr _ _ _ (Val last tb) ?e2 ?t2,
    Heq : is_true (eq_type ?t1 ?t2) |- _ =>
    pose proof (type_rel_typeof _ _ _ _ _ _ Hfirst) as Ha;
    pose proof (type_rel_typeof _ _ _ _ _ _ Hlast) as Hb;
    simpl in Ha, Hb; subst t1 t2;
    apply eq_type_sound in Heq; subst tb;
    pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hfirst) as He1;
    pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hlast) as He2;
    subst e1 e2;
    pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hfirst) as Hshape1;
    pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hlast) as Hshape2
  end.
  destruct ta; simpl in *; try discriminate.
  eexists. repeat split; eauto.
Qed.

Lemma coherent_loop_entered_configuration :
  forall ge Gamma Sigma vm m objects cells packets body ef count,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets body ef Utype ->
  exists effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
      (match count with O => Val Vunit Utype | S remaining => LoopFrame remaining body body end)
      effect Utype /\ sub_effect effect ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets body ef count
    [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct count as [|remaining].
  - exists nil. split; [|apply sub_effect_nil]. split; [|exact Hcoherent].
    constructor; simpl; auto. apply ty_valu.
  - exists ef. split; [|apply sub_effect_refl]. split; [|exact Hcoherent].
    constructor; simpl; auto. eapply ty_loopframe; eauto using sub_effect_refl.
Qed.

Theorem coherent_loop_entry_progress :
  forall ge Gamma Sigma vm m objects cells packets p first ta last tb d body ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (For (Val first ta) (Val last tb) d body Utype) ef Utype ->
  exists next effect,
    ssem_expr ge p vm m (For (Val first ta) (Val last tb) d body Utype) m vm next /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets next effect Utype /\
    sub_effect effect ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p first ta last tb d body ef
    [[Hheap Htyped [_ [_ Hloc]] [_ [_ Hframes]]] Hcoherent].
  destruct (typed_loop_value_bounds _ _ _ _ _ _ _ _ _ _ Htyped)
    as [pt [Ha [Hb [Hfirst [Hlast [Hnumeric Hbody]]]]]]. subst ta tb.
  destruct (primitive_loop_bounds_total d pt first last Hfirst Hlast Hnumeric)
    as [n [Hcount Hnonnegative]].
  assert (Hconfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets body ef Utype)
    by (split; [constructor; assumption |exact Hcoherent]).
  destruct (coherent_loop_entered_configuration _ _ _ _ _ _ _ _ _ _ (Z.to_nat n) Hconfig)
    as [effect [Hnext Hsub]].
  eexists; exists effect. split; [apply ssem_for3; exact Hcount |]. split; assumption.
Qed.

Theorem coherent_loop_entry_preservation :
  forall ge Gamma Sigma vm m objects cells packets p first ta last tb d body ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (For (Val first ta) (Val last tb) d body Utype) ef Utype ->
  ssem_expr ge p vm m (For (Val first ta) (Val last tb) d body Utype) final vm' next ->
  final = m /\ vm' = vm /\ exists effect,
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next effect Utype /\
    sub_effect effect ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p first ta last tb d body ef final vm' next
    [[Hheap Htyped [_ [_ Hloc]] [_ [_ Hframes]]] Hcoherent] Hstep.
  destruct (typed_loop_value_bounds _ _ _ _ _ _ _ _ _ _ Htyped)
    as [pt [Ha [Hb [Hfirst [Hlast [Hnumeric Hbody]]]]]].
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  split; [reflexivity |]. split; [reflexivity |].
  apply coherent_loop_entered_configuration. split; [constructor; assumption |exact Hcoherent].
Qed.

Lemma coherent_loop_frame_components :
  forall ge Gamma Sigma vm m objects cells packets remaining template active budget,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (LoopFrame remaining template active) budget Utype ->
  exists active_effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets template budget Utype /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets active active_effect Utype /\
    sub_effect active_effect budget = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets remaining template active budget
    [[Hheap Htyped [HtemplateLoc HactiveLoc] [HtemplateFrames HactiveFrames]] Hcoherent].
  inversion Htyped; subst. eexists. split; [split; [constructor; eassumption |assumption] |].
  split; [split; [constructor; eassumption |assumption] |assumption].
Qed.

Theorem coherent_loop_frame_progress_from_body :
  forall ge Gamma Sigma vm m objects cells packets p remaining template active budget,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (LoopFrame remaining template active) budget Utype ->
  (forall active_effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets active active_effect Utype ->
    (exists v annotation, active = Val v annotation) \/
      exists final vm' next, ssem_expr ge p vm m active final vm' next) ->
  exists final vm' next,
    ssem_expr ge p vm m (LoopFrame remaining template active) final vm' next.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p remaining template active budget Hconfig Hchild.
  destruct (coherent_loop_frame_components _ _ _ _ _ _ _ _ _ _ _ _ Hconfig)
    as [active_effect [Htemplate [Hactive Hsub]]].
  destruct (Hchild active_effect Hactive) as [[v [annotation He]] | [final [vm' [next Hstep]]]].
  - subst active. pose proof (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hactive)) as Htyped.
    inversion Htyped; subst. destruct remaining; do 3 eexists.
    + apply ssem_loop_frame_done.
    + apply ssem_loop_frame_restart.
  - do 3 eexists. apply ssem_loop_frame_step. exact Hstep.
Qed.

Theorem coherent_loop_frame_preservation_from_body :
  forall ge Gamma Sigma vm m objects cells packets p remaining template active budget final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (LoopFrame remaining template active) budget Utype ->
  (forall active_effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets active active_effect Utype ->
    forall nextM nextVm nextActive,
      ssem_expr ge p vm m active nextM nextVm nextActive ->
      exists Sigma' objects' cells' packets' effect',
        initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
        coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextActive effect' Utype /\
        sub_effect effect' active_effect = true) ->
  ssem_expr ge p vm m (LoopFrame remaining template active) final vm' next ->
  exists Sigma' objects' cells' packets' effect,
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next effect Utype /\
    sub_effect effect budget = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p remaining template active budget final vm' next Hconfig Hchild Hstep.
  destruct (coherent_loop_frame_components _ _ _ _ _ _ _ _ _ _ _ _ Hconfig)
    as [active_effect [Htemplate [Hactive Hsub]]].
  pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ (proj1 Htemplate)) as Hheap.
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr ge p vm m active _ _ _ |- _ =>
      destruct (Hchild active_effect Hactive _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hdecrease]]]]]]]
    end.
    pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
    destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (proj1 Htemplate) Hupdate Hheap') as [_ Htemplate' HtemplateLoc' HtemplateFrames'].
    destruct Hnew as [_ Hactive' HactiveLoc' HactiveFrames'].
    exists Sigma', objects', cells', packets', budget. split; [exact Hupdate |]. split; [|apply sub_effect_refl].
    split; [constructor; simpl; auto |exact Hcoherent'].
    eapply ty_loopframe; [exact Htemplate' |exact Hactive' |]. eapply sub_effect_trans; eauto.
  - exists Sigma, objects, cells, packets, nil. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [|apply sub_effect_nil]. split; [|exact (proj2 Htemplate)].
      constructor; simpl; auto. apply ty_valu.
  - exists Sigma, objects, cells, packets, budget. split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split; [|apply sub_effect_refl].
      destruct Htemplate as [[_ Htyped Hloc Hframes] Hcoherent].
      split; [|exact Hcoherent]. constructor; simpl; auto.
      eapply ty_loopframe; eauto using sub_effect_refl.
Qed.

Print Assumptions coherent_loop_entry_progress.
Print Assumptions coherent_loop_entry_preservation.
Print Assumptions coherent_loop_frame_progress_from_body.
Print Assumptions coherent_loop_frame_preservation_from_body.
