(* Evaluated control heads preserve the shared initialized heap. These are
   unconditional head cases, not preservation of unevaluated child contexts. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory.
Require Import BeePL_substitution_proofs BeePL_runtime_locations BeePL_aggregate_memory.
Require Import BeePL_initialized_runtime BeePL_initialized_substitution.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Theorem initialized_conditional_head : forall ge Gamma Sigma vm m objects cells packets p b yes no ef ty,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty) ef ty ->
  ssem_expr ge p vm m (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty)
    m vm (if b then yes else no) /\
  exists selected_effect, sub_effect selected_effect ef = true /\
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
      (if b then yes else no) selected_effect ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b yes no ef ty
    [Hheap Htyping Hlocations Hframes].
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyping)
    as [guard_effect [budget [yes_effect [no_effect
      [Heffect [Hguard [Hyes [Hno [HyesBound HnoBound]]]]]]]]].
  pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hguard) as Hnil.
  subst guard_effect. simpl in Heffect. subst ef.
  destruct Hlocations as [_ [Hyesloc Hnoloc]]. destruct Hframes as [_ [Hyesframes Hnoframes]].
  destruct b; simpl; split.
  - pose proof (type_rel_typeof _ _ _ _ _ _ Hyes) as Hannotation.
    rewrite <- Hannotation. apply ssem_ctrue.
  - exists yes_effect. split; [exact HyesBound |]. constructor; assumption.
  - pose proof (type_rel_typeof _ _ _ _ _ _ Hno) as Hannotation.
    rewrite <- Hannotation. apply ssem_cfalse.
  - exists no_effect. split; [exact HnoBound |]. constructor; assumption.
Qed.

Theorem initialized_conditional_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b yes no ef ty final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty) ef ty ->
  ssem_expr ge p vm m (Cond (Val (Vbool b) (Vtype Tbool)) yes no ty) final vm' e' ->
  final = m /\ vm' = vm /\
  exists selected_effect, sub_effect selected_effect ef = true /\
    initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' selected_effect ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b yes no ef ty final vm' e' Hconfig Hstep.
  pose proof (proj2 (initialized_conditional_head ge Gamma Sigma vm m objects cells packets p b yes no ef ty Hconfig)) as Hresult.
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: split; [reflexivity |]; split; [reflexivity |]; exact Hresult.
Qed.

Theorem initialized_none_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p ty ef final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Enone ty) ef ty ->
  ssem_expr ge p vm m (Enone ty) final vm' e' ->
  final = m /\ vm' = vm /\
  initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p ty ef final vm' e'
    [Hheap Htyping Hlocations Hframes] Hstep.
  destruct (none_step_preservation _ _ _ _ _ _ _ _ _ _ _ _ Htyping Hstep) as [Hm [Hvm Htyped]].
  inversion Hstep; subst. split; [reflexivity |]. split; [reflexivity |].
  constructor; auto.
Qed.

Theorem initialized_some_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p v annotation ty ef final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Esome (Val v annotation) ty) ef ty ->
  ssem_expr ge p vm m (Esome (Val v annotation) ty) final vm' e' ->
  final = m /\ vm' = vm /\
  initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p v annotation ty ef final vm' e'
    [Hheap Htyping Hlocations Hframes] Hstep.
  destruct (some_value_step_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htyping Hstep)
    as [Hm [Hvm Htyped]].
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  split; [reflexivity |]. split; [reflexivity |]. constructor; auto.
  destruct (some_typing_components _ _ _ _ _ _ Htyping) as [pt [Hty Hoperand]]. subst ty.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation.
  simpl in Hannotation. subst annotation. exact Hlocations.
Qed.

Lemma initialized_option_match_head_invariants :
  forall ge Sigma cells objects packets L p vm m o pt ps es ty final vm' e',
  runtime_locations L (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) ->
  initialized_runtime_frames ge Sigma cells objects packets (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) ->
  ssem_expr ge p vm m (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) final vm' e' ->
  runtime_locations L e' /\ initialized_runtime_frames ge Sigma cells objects packets e'.
Proof.
  intros ge Sigma cells objects packets L p vm m o pt ps es ty final vm' e' Hlocations Hframes Hstep.
  inversion Hstep; subst; cbn [runtime_locations all_expr_locations value_locations initialized_runtime_frames] in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  - destruct Hlocations as [_ [Hfirst [Hsecond _]]]. destruct Hframes as [_ [Hfirstf [Hsecondf _]]].
    destruct (eq_pattern p1 Pnone); split; assumption.
  - destruct Hlocations as [Hpayload [_ [Hsome _]]]. destruct Hframes as [_ [_ [Hsomef _]]].
    split; [eapply value_substitution_runtime_locations; eauto |].
    apply value_substitution_initialized_runtime_frames; exact Hsomef.
  - destruct Hlocations as [Hpayload [Hsome _]]. destruct Hframes as [_ [Hsomef _]].
    split; [eapply value_substitution_runtime_locations; eauto |].
    apply value_substitution_initialized_runtime_frames; exact Hsomef.
Qed.

Theorem initialized_option_match_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p o pt ps es ef ty final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) ef ty ->
  ssem_expr ge p vm m (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) final vm' e' ->
  final = m /\ vm' = vm /\ exists ef', sub_effect ef' ef = true /\
    initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' ef' ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p o pt ps es ef ty final vm' e'
    [Hheap Htyping Hlocations Hframes] Hstep.
  destruct (option_match_value_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htyping Hstep)
    as [Hm [Hvm [ef' [Htyped Hsub]]]].
  destruct (initialized_option_match_head_invariants _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlocations Hframes Hstep)
    as [Hlocated Hframed].
  subst final vm'. split; [reflexivity |]. split; [reflexivity |].
  exists ef'. split; [exact Hsub |]. constructor; assumption.
Qed.

Theorem initialized_option_match_head_progress :
  forall ge Gamma Sigma vm m objects cells packets p o pt ps es ef ty,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) ef ty ->
  exists e' ef',
    ssem_expr ge p vm m (Match (Val (Voption o) (Ptrtype (Otype pt))) ps es ty) m vm e' /\
    sub_effect ef' ef = true /\
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e' ef' ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p o pt ps es ef ty Hconfig.
  destruct (option_match_value_progress ge.(genv_cenv) Gamma Sigma ge p vm m o pt ps es ef ty
    (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ Hconfig)) as [e' Hstep].
  destruct (initialized_option_match_head_preservation ge Gamma Sigma vm m objects cells packets p o pt ps es ef ty m vm e' Hconfig Hstep)
    as [_ [_ [ef' [Hsub Hfinal]]]]. exists e', ef'. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions initialized_conditional_head_preservation.
Print Assumptions initialized_none_head_preservation.
Print Assumptions initialized_some_head_preservation.
Print Assumptions initialized_option_match_head_preservation.
Print Assumptions initialized_option_match_head_progress.

Require Import BeePL_auxlemmas BeePL_initialized_lists.

(* Context lifting consumes the child preservation induction hypothesis. It
   does not assert preservation for arbitrary child expressions. *)
Theorem initialized_conditional_context :
  forall ge Gamma Sigma vm m objects cells packets p guard yes no ef ty final vm' guard',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Cond guard yes no ty) ef ty ->
  ssem_expr ge p vm m guard final vm' guard' ->
  (forall guard_effect,
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets guard guard_effect (Vtype Tbool) ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' guard' effect' (Vtype Tbool) /\
      sub_effect effect' guard_effect = true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (Cond guard yes no ty) final vm' (Cond guard' yes no ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' (Cond guard' yes no ty) ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p guard yes no ef ty final vm' guard'
    Hconfig Hstep Hchild.
  destruct Hconfig as [Hheap Htyping [HguardLoc [HyesLoc HnoLoc]] [HguardFrames [HyesFrames HnoFrames]]].
  destruct (conditional_typing_components _ _ _ _ _ _ _ _ Htyping)
    as [geffect [beffect [yes_effect [no_effect
      [Heffect [Hguard [Hyes [Hno [HyesBound HnoBound]]]]]]]]]. subst ef.
  assert (HguardConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets guard geffect (Vtype Tbool))
    by (constructor; assumption).
  destruct (Hchild geffect HguardConfig) as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [Hnew Hsub]]]]]]].
  assert (HyesConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets yes yes_effect ty)
    by (constructor; assumption).
  assert (HnoConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets no no_effect ty)
    by (constructor; assumption).
  pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HyesConfig Hupdate Hheap')
    as [_ Hyes' HyesLoc' HyesFrames'].
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HnoConfig Hupdate Hheap')
    as [_ Hno' HnoLoc' HnoFrames'].
  destruct Hnew as [_ Hguard' HguardLoc' HguardFrames'].
  exists Sigma', objects', cells', packets', (effect' ++ beffect). split.
  - pose proof (type_rel_typeof _ _ _ _ _ _ Hyes) as Hannotation.
    rewrite <- Hannotation. apply ssem_cond; exact Hstep.
  - split; [exact Hupdate |]. split.
    + constructor; simpl; auto. eapply ty_cond; eassumption.
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
Qed.

Theorem initialized_some_context :
  forall ge Gamma Sigma vm m objects cells packets p operand ef ty final vm' operand',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Esome operand ty) ef ty ->
  ssem_expr ge p vm m operand final vm' operand' ->
  (forall operandTy,
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef operandTy ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' operand' effect' operandTy /\
      sub_effect effect' ef = true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (Esome operand ty) final vm' (Esome operand' ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' (Esome operand' ty) ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p operand ef ty final vm' operand'
    [Hheap Htyping Hlocations Hframes] Hstep Hchild.
  inversion Htyping; subst.
  match goal with Hoperand : type_expr _ _ _ operand ef (Ptrtype ?pt) |- _ =>
    assert (Hconfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Ptrtype pt))
      by (constructor; assumption);
    destruct (Hchild _ Hconfig) as [Sigma' [objects' [cells' [packets' [ef' [Hupdate [Hnew Hsub]]]]]]]
  end.
  exists Sigma', objects', cells', packets', ef'. split; [apply ssem_some1; exact Hstep |].
  split; [exact Hupdate |]. split; [|exact Hsub].
  destruct Hnew as [Hheap' Htyped' Hlocated' Hframed']. constructor; simpl; auto.
  eapply ty_some; eauto.
Qed.

(* The operational scrutinee context has exactly two patterns and branches.
   This lemma covers both option orders and the existing two-branch Bytes
   schema; it does not claim a context rule for arbitrary-length matches. *)
Theorem initialized_match_context :
  forall ge Gamma Sigma vm m objects cells packets p scrutinee pat1 pat2 yes no ef ty final vm' scrutinee',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Match scrutinee [pat1; pat2] [yes; no] ty) ef ty ->
  ssem_expr ge p vm m scrutinee final vm' scrutinee' ->
  (forall scrutineeEffect scrutineeTy,
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets scrutinee scrutineeEffect scrutineeTy ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' scrutinee' effect' scrutineeTy /\
      sub_effect effect' scrutineeEffect = true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (Match scrutinee [pat1; pat2] [yes; no] ty)
      final vm' (Match scrutinee' [pat1; pat2] [yes; no] ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets'
      (Match scrutinee' [pat1; pat2] [yes; no] ty) ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p scrutinee pat1 pat2 yes no ef ty final vm' scrutinee'
    Hconfig Hstep Hchild.
  pose proof Hconfig as Hparts. destruct Hparts as [Hheap Htyping [HscrutLoc HbranchesLoc] [HscrutFrames HbranchesFrames]].
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyping)
    as [_ [seffect [sty [beffect [effects [Heffect [Hscrut [Hpatterns [Hlength [Hbranches Heffects]]]]]]]]]].
  subst ef.
  assert (HscrutConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets scrutinee seffect sty)
    by (constructor; assumption).
  destruct (Hchild seffect sty HscrutConfig) as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [Hnew Hsub]]]]]]].
  pose proof (initialized_evolution_store _ _ _ _ _ _ _ _ _ _ Hupdate) as Hext.
  pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hupdate Hheap')
    as [_ _ [_ HbranchesLoc'] [_ HbranchesFrames']].
  destruct Hnew as [_ Hscrut' HscrutLoc' HscrutFrames'].
  exists Sigma', objects', cells', packets', (effect' ++ beffect). split; [apply ssem_match_none1; exact Hstep |].
  split; [exact Hupdate |]. split.
  - constructor; simpl; auto.
    eapply ty_matcho with (te := sty) (branch_effect := effects); eauto using type_infer_match_schemas.
    intros n pat branch Hpat Hbranch.
    eapply (proj2 typing_store_extension); [eapply Hbranches; eauto | exact Hext].
  - apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
Qed.

Print Assumptions initialized_conditional_context.
Print Assumptions initialized_some_context.
Print Assumptions initialized_match_context.
