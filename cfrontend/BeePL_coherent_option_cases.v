(* Coherent optional-value and match expression cases. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_initialized_runtime BeePL_initialized_control.
Require Import BeePL_initialized_lists BeePL_coherent_configurations.
Import ListNotations.

Theorem coherent_some_context :
  forall ge Gamma Sigma vm m objects cells packets p operand ef ty final vm' operand',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Esome operand ty) ef ty ->
  ssem_expr ge p vm m operand final vm' operand' ->
  (forall operandTy,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef operandTy ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' operand' effect' operandTy /\
      sub_effect effect' ef = true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (Esome operand ty) final vm' (Esome operand' ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' (Esome operand' ty) ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p operand ef ty final vm' operand'
    [[Hheap Htyping Hlocations Hframes] Hcoherent] Hstep Hchild.
  inversion Htyping; subst.
  match goal with Hoperand : type_expr _ _ _ operand ef (Ptrtype ?pt) |- _ =>
    assert (Hconfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Ptrtype pt))
      by (split; [constructor; assumption|exact Hcoherent]);
    destruct (Hchild _ Hconfig) as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [Hnew Hsub]]]]]]]
  end.
  exists Sigma', objects', cells', packets', ef'. split; [apply ssem_some1; exact Hstep |].
  split; [exact Hupdate |]. split; [|exact Hsub].
  destruct Hnew as [[Hheap' Htyped' Hlocated' Hframed'] Hcoherent']. split; [|exact Hcoherent']. constructor; simpl; auto.
  eapply ty_some; eauto.
Qed.

Theorem coherent_match_context :
  forall ge Gamma Sigma vm m objects cells packets p scrutinee pat1 pat2 yes no ef ty final vm' scrutinee',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match scrutinee [pat1; pat2] [yes; no] ty) ef ty ->
  ssem_expr ge p vm m scrutinee final vm' scrutinee' ->
  (forall scrutineeEffect scrutineeTy,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets scrutinee scrutineeEffect scrutineeTy ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' scrutinee' effect' scrutineeTy /\
      sub_effect effect' scrutineeEffect = true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (Match scrutinee [pat1; pat2] [yes; no] ty)
      final vm' (Match scrutinee' [pat1; pat2] [yes; no] ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets'
      (Match scrutinee' [pat1; pat2] [yes; no] ty) ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p scrutinee pat1 pat2 yes no ef ty final vm' scrutinee'
    Hconfig Hstep Hchild.
  pose proof Hconfig as Hparts. destruct Hparts as [[Hheap Htyping [HscrutLoc HbranchesLoc] [HscrutFrames HbranchesFrames]] Hcoherent].
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyping)
    as [_ [seffect [sty [beffect [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  subst ef.
  assert (HscrutConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets scrutinee seffect sty)
    by (split; [constructor; assumption|exact Hcoherent]).
  destruct (Hchild seffect sty HscrutConfig) as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]].
  pose proof (initialized_evolution_store _ _ _ _ _ _ _ _ _ _ Hupdate) as Hext.
  pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig) Hupdate Hheap')
    as [_ _ [_ HbranchesLoc'] [_ HbranchesFrames']].
  destruct Hnew as [_ Hscrut' HscrutLoc' HscrutFrames'].
  exists Sigma', objects', cells', packets', (effect' ++ beffect). split; [apply ssem_match_none1; exact Hstep |].
  split; [exact Hupdate |]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto.
    eapply ty_matcho with (te := sty) (branch_effect := effects); eauto using type_infer_match_schemas.
    intros n pat branch Hpat Hbranch.
    eapply (proj2 typing_store_extension); [eapply Hbranches; eauto | exact Hext].
  - apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
Qed.


Theorem coherent_some_progress_from_operand : forall ge Gamma Sigma vm m objects cells packets p operand ef ty,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Esome operand ty) ef ty ->
  (forall operandTy,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef operandTy ->
    (exists v annotation, operand=Val v annotation) \/ exists final vm' next, ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next, ssem_expr ge p vm m (Esome operand ty) final vm' next.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hchild. inversion Htyped; subst.
  match goal with Hoperand : type_expr _ _ _ operand ef (Ptrtype ?pt) |- _ =>
    assert (Hconfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Ptrtype pt))
      by (split; [constructor; assumption|exact Hcoherent]);
    destruct (Hchild _ Hconfig) as [[v [annotation Heq]]|[final [vm' [next Hstep]]]] end.
  - subst operand. do 3 eexists; apply ssem_some2.
  - do 3 eexists; apply ssem_some1; exact Hstep.
Qed.

Theorem coherent_some_preservation_from_operand : forall ge Gamma Sigma vm m objects cells packets p operand ef ty final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Esome operand ty) ef ty ->
  (forall operandTy,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef operandTy ->
    forall nextM nextVm nextOperand, ssem_expr ge p vm m operand nextM nextVm nextOperand ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextOperand effect' operandTy /\
      sub_effect effect' ef=true) ->
  ssem_expr ge p vm m (Esome operand ty) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hchild Hstep. inversion Hstep; subst.
  - match goal with Hs : ssem_expr _ _ _ _ operand _ _ _ |- _ =>
      destruct (coherent_some_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig Hs
        ltac:(intros operandTy Hoperand; eapply Hchild; eauto))
        as [Sigma' [objects' [cells' [packets' [ef' [_ [Hevolve [Hresult Hsub]]]]]]]] end.
    exists Sigma', objects', cells', packets', ef'. auto.
  - destruct (initialized_some_head_preservation _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ (proj1 Hconfig) Hstep)
      as [_ [_ Hresult]].
    exists Sigma, objects, cells, packets, nil. split.
    + eapply initialized_heap_evolution_refl. exact(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)).
    + split; [split; [exact Hresult|exact(proj2 Hconfig)]|apply sub_effect_nil].
Qed.

Theorem coherent_none_progress : forall ge Gamma Sigma vm m objects cells packets p ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Enone ty) ef ty ->
  exists next, ssem_expr ge p vm m (Enone ty) m vm next /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets next ef ty.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent]. inversion Htyped; subst.
  exists (Val (Voption None) (Ptrtype (Otype t))). split; [apply ssem_none|].
  split; [eapply initialized_heap_evolution_refl; exact Hheap|].
  split; [|exact Hcoherent]. constructor; auto. constructor; [assumption|intros; discriminate].
Qed.

Theorem coherent_none_preservation : forall ge Gamma Sigma vm m objects cells packets p ty ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Enone ty) ef ty ->
  ssem_expr ge p vm m (Enone ty) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hstep.
  destruct(initialized_none_head_preservation _ _ _ _ _ _ _ _ p _ _ _ _ _ (proj1 Hconfig) Hstep)
    as [Hm [Hvm Hresult]]. subst final vm'.
  exists Sigma, objects, cells, packets, nil. split.
  - eapply initialized_heap_evolution_refl. exact(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)).
  - split; [split; [exact Hresult|exact(proj2 Hconfig)]|apply sub_effect_nil].
Qed.

Theorem coherent_option_match_head_progress : forall ge Gamma Sigma vm m objects cells packets p payload pt patterns branches ef ty,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match (Val (Voption payload) (Ptrtype (Otype pt))) patterns branches ty) ef ty ->
  exists next effect,
    ssem_expr ge p vm m (Match (Val (Voption payload) (Ptrtype (Otype pt))) patterns branches ty) m vm next /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets next effect ty /\ sub_effect effect ef=true.
Proof.
  intros * [Hconfig Hcoherent].
  destruct(initialized_option_match_head_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig)
    as [next [effect [Hstep [Hsub Hfinal]]]].
  exists next, effect. split; [exact Hstep|]. split.
  - eapply initialized_heap_evolution_refl. exact(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hconfig).
  - split; [split; assumption|exact Hsub].
Qed.

Theorem coherent_option_match_head_preservation : forall ge Gamma Sigma vm m objects cells packets p payload pt patterns branches ef ty final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match (Val (Voption payload) (Ptrtype (Otype pt))) patterns branches ty) ef ty ->
  ssem_expr ge p vm m (Match (Val (Voption payload) (Ptrtype (Otype pt))) patterns branches ty) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * [Hconfig Hcoherent] Hstep.
  destruct(initialized_option_match_head_preservation _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ Hconfig Hstep)
    as [Hm [Hvm [effect [Hsub Hfinal]]]]. subst final vm'.
  exists Sigma, objects, cells, packets, effect. split.
  - eapply initialized_heap_evolution_refl. exact(initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hconfig).
  - split; [split; assumption|exact Hsub].
Qed.
Print Assumptions coherent_some_preservation_from_operand.
Print Assumptions coherent_match_context.
Print Assumptions coherent_none_preservation.
Print Assumptions coherent_option_match_head_preservation.
