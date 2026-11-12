(* Bind and internal-call frame cases for the whole-expression induction. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_initialized_runtime BeePL_initialized_substitution BeePL_coherent_configurations.
Import ListNotations.

Theorem coherent_bind_progress_from_initializer : forall ge Gamma Sigma vm m objects cells packets p x tx init body rt ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Bind x tx init body rt) ef rt ->
  (forall effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets init effect tx ->
    (exists v annotation, init=Val v annotation) \/ exists final vm' next, ssem_expr ge p vm m init final vm' next) ->
  exists final vm' next, ssem_expr ge p vm m (Bind x tx init body rt) final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [Hiloc Hbloc] [Hiframes Hbframes]] Hcoherent].
  destruct (bind_typing_components _ _ _ _ _ _ _ _ _ Htyped) as [ei [eb [Hef [Hi Hb]]]].
  assert (Hinit : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets init ei tx)
    by (split; [constructor; assumption|exact Hcoherent]).
  destruct (Hchild ei Hinit) as [[v [annotation Heq]]|[final [vm' [next Hstep]]]].
  - subst init. pose proof(type_rel_typeof _ _ _ _ _ _ Hi) as Hannotation; simpl in Hannotation; subst annotation.
    destruct (initialized_bind_value_progress _ _ _ p _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)) as [Hstep _].
    do 3 eexists; exact Hstep.
  - pose proof(type_rel_typeof _ _ _ _ _ _ Hb) as Hannotation.
    rewrite <- Hannotation. do 3 eexists. apply ssem_bind1; exact Hstep.
Qed.

Theorem coherent_bind_preservation_from_initializer : forall ge Gamma Sigma vm m objects cells packets p x tx init body rt ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Bind x tx init body rt) ef rt ->
  (forall effect,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets init effect tx ->
    forall nextM nextVm nextInit, ssem_expr ge p vm m init nextM nextVm nextInit ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextInit effect' tx /\
      sub_effect effect' effect=true) ->
  ssem_expr ge p vm m (Bind x tx init body rt) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' rt /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hiloc Hbloc] [Hiframes Hbframes]] Hcoherent].
  destruct (bind_typing_components _ _ _ _ _ _ _ _ _ Htyped) as [ei [eb [Hef [Hi Hb]]]]. subst ef.
  assert (Hinit : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets init ei tx)
    by (split; [constructor; assumption|exact Hcoherent]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ init _ _ _ |- _ =>
      destruct (Hchild ei Hinit _ _ _ Hs) as [Sigma' [objects' [cells' [packets' [ei' [Hevolve [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    match goal with Hs : ssem_expr _ _ _ _ init _ _ _ |- _ =>
      destruct (initialized_bind_initializer_step _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (proj1 Hconfig) Hi Hb Hs Hevolve Hnew Hsub) as [_ [Hresult Hsubresult]] end.
    exists Sigma', objects', cells', packets', (ei'++eb). split; [exact Hevolve|]. split; [split; assumption|exact Hsubresult].
  - destruct (initialized_bind_value_preservation _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig) Hstep)
      as [Hm [Hvm Hresult]].
    exists Sigma, objects, cells, packets, (ei++eb). split; [eapply initialized_heap_evolution_refl; exact Hheap|].
    split; [split; assumption|apply sub_effect_refl].
Qed.

Theorem coherent_callframe_progress_from_body : forall ge Gamma Sigma caller callee m objects cells packets p body ef ty,
  coherent_runtime_configuration ge Gamma Sigma caller m objects cells packets (CallFrame callee body ty) ef ty ->
  (forall calleeGamma,
    coherent_runtime_configuration ge calleeGamma Sigma callee m objects cells packets body ef ty ->
    (exists v annotation, body=Val v annotation) \/ exists final callee' next, ssem_expr ge p callee m body final callee' next) ->
  exists final caller' next, ssem_expr ge p caller m (CallFrame callee body ty) final caller' next.
Proof.
  intros * [Hconfig Hcoherent] Hchild.
  destruct(initialized_frame_configuration_body _ _ _ _ _ _ _ _ _ _ _ _ Hconfig) as [calleeGamma Hbody].
  destruct(Hchild calleeGamma (conj Hbody Hcoherent)) as [[v [annotation Heq]]|[final [callee' [next Hstep]]]].
  - subst body. pose proof(type_rel_typeof _ _ _ _ _ _ (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ Hbody)) as Hannotation.
    simpl in Hannotation; subst annotation. do 3 eexists; apply ssem_call_frame_return.
  - do 3 eexists; apply ssem_call_frame_step; exact Hstep.
Qed.

Theorem coherent_callframe_preservation_from_body : forall ge Gamma Sigma caller callee m objects cells packets p body ef ty final caller' next,
  coherent_runtime_configuration ge Gamma Sigma caller m objects cells packets (CallFrame callee body ty) ef ty ->
  (forall calleeGamma,
    coherent_runtime_configuration ge calleeGamma Sigma callee m objects cells packets body ef ty ->
    forall nextM nextVm nextBody, ssem_expr ge p callee m body nextM nextVm nextBody ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge calleeGamma Sigma' nextVm nextM objects' cells' packets' nextBody effect' ty /\
      sub_effect effect' ef=true) ->
  ssem_expr ge p caller m (CallFrame callee body ty) final caller' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' caller' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * [Hconfig Hcoherent] Hchild Hstep.
  pose proof(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hconfig) as Hheap.
  destruct(initialized_frame_configuration_body _ _ _ _ _ _ _ _ _ _ _ _ Hconfig) as [calleeGamma Hbody].
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ body _ _ _ |- _ =>
      destruct(Hchild calleeGamma (conj Hbody Hcoherent) _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hevolve [[Hnew Hcoherent'] Hsub]]]]]]];
      destruct(initialized_frame_body_step _ p _ calleeGamma _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hs Hnew Hevolve Hsub) as [_ [Hresult Hsubresult]] end.
    exists Sigma', objects', cells', packets', effect'. split; [exact Hevolve|]. split; [split; assumption|exact Hsubresult].
  - destruct(initialized_frame_return _ p _ _ _ _ _ _ _ _ _ _ _ Hconfig) as [_ Hresult].
    exists Sigma, objects, cells, packets, ef. split; [eapply initialized_heap_evolution_refl; exact Hheap|].
    split; [split; assumption|apply sub_effect_refl].
Qed.
Print Assumptions coherent_bind_preservation_from_initializer.
Print Assumptions coherent_callframe_preservation_from_body.
