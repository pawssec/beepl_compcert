(* Full source For cases. Incremental LoopFrame body cases are proved in
   BeePL_coherent_loops; these wrappers assemble both bound contexts and entry. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_loops BeePL_coherent_loop_contexts.
Import ListNotations.

Theorem coherent_for_progress_from_bounds : forall ge Gamma Sigma vm m objects cells packets p first last d body ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(For first last d body ty)ef ty ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets first effect boundType ->
    (exists value annotation,first=Val value annotation) \/ exists final vm' next,ssem_expr ge p vm m first final vm' next) ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets last effect boundType ->
    (exists value annotation,last=Val value annotation) \/ exists final vm' next,ssem_expr ge p vm m last final vm' next) ->
  exists final vm' next,ssem_expr ge p vm m(For first last d body ty)final vm' next.
Proof.
  intros * Hconfig HfirstChild HlastChild.
  pose proof Hconfig as [[Hheap Htyped [Hfloc [Hlloc Hbloc]] [Hfframes [Hlframes Hbframes]]] Hcoherent].
  destruct(for_typing_effect_components _ _ _ _ _ _ _ _ _ Htyped)
    as [t1 [t2 [e1 [e2 [eb [Hty [Hef [Hfirst [Hlast Hrest]]]]]]]]]. subst ty.
  assert(HfirstConfig:coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets first e1 t1)
    by(split;[constructor;assumption|exact Hcoherent]).
  assert(HlastConfig:coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets last e2 t2)
    by(split;[constructor;assumption|exact Hcoherent]).
  destruct(HfirstChild _ _ HfirstConfig) as [[firstValue [firstAnnotation HfirstEq]]|[final [vm' [next Hstep]]]].
  - subst first. destruct(HlastChild _ _ HlastConfig) as [[lastValue [lastAnnotation HlastEq]]|[final [vm' [next Hstep]]]].
    + subst last. destruct(coherent_loop_entry_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ Hconfig)
        as [next [effect [Hstep Hfinal]]]. do 3 eexists; exact Hstep.
    + do 3 eexists; apply ssem_for2;exact Hstep.
  - do 3 eexists;apply ssem_for1;exact Hstep.
Qed.

Theorem coherent_for_preservation_from_bounds : forall ge Gamma Sigma vm m objects cells packets p first last d body ty ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(For first last d body ty)ef ty ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets first effect boundType ->
    forall nextM nextVm nextBound,ssem_expr ge p vm m first nextM nextVm nextBound ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextBound effect' boundType /\ sub_effect effect' effect=true) ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets last effect boundType ->
    forall nextM nextVm nextBound,ssem_expr ge p vm m last nextM nextVm nextBound ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextBound effect' boundType /\ sub_effect effect' effect=true) ->
  ssem_expr ge p vm m(For first last d body ty)final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig HfirstChild HlastChild Hstep.
  pose proof (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)) as Htyped.
  assert(Hty:ty=Utype) by(inversion Htyped;subst;reflexivity). subst ty.
  inversion Hstep; subst.
  - match goal with Hs:ssem_expr _ _ _ _ first _ _ _ |- _ =>
      destruct(coherent_for_first_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ Hconfig Hs
        ltac:(intros effect boundType Hbound; eapply HfirstChild; eauto))
        as [Sigma' [objects' [cells' [packets' [effect' [_ [Hevolve [Hfinal Hsub]]]]]]]] end.
    exists Sigma',objects',cells',packets',effect';auto.
  - match goal with Hs:ssem_expr _ _ _ _ last _ _ _ |- _ =>
      destruct(coherent_for_last_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ Hconfig Hs
        ltac:(intros effect boundType Hbound; eapply HlastChild; eauto))
        as [Sigma' [objects' [cells' [packets' [effect' [_ [Hevolve [Hfinal Hsub]]]]]]]] end.
    exists Sigma',objects',cells',packets',effect';auto.
  - destruct(coherent_loop_entry_preservation _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [_ [_ [effect [Hfinal Hsub]]]].
    exists Sigma,objects,cells,packets,effect;split.
    + eapply initialized_heap_evolution_refl. exact(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)).
    + auto.
Qed.
Print Assumptions coherent_for_progress_from_bounds.
Print Assumptions coherent_for_preservation_from_bounds.
