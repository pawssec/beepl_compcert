(* Operator cases for the shared initialized, coherent runtime state.  Head
   results use the checked machine-integer semantics; context cases consume
   only recursive child hypotheses and retain suspended operands. *)
Require Import List Bool Integers AST Maps Memory Ctypes Cop.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_auxlemmas BeePL_soundness_memory.
Require Import BeePL_soundness_operators BeePL_runtime_locations BeePL_aggregate_memory.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Require Import BeePL_layout_coherence BeePL_soundness_store.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Lemma binary_typing_components : forall cenv Gamma Sigma op left right rt ef,
  type_expr cenv Gamma Sigma (Prim (Bop op) [left; right] rt) ef rt ->
  exists ty ef1 ef2, ef = ef1 ++ ef2 /\
    type_expr cenv Gamma Sigma left ef1 ty /\
    type_expr cenv Gamma Sigma right ef2 ty /\
    (forall nextSigma nextLeft nextRight nextEf1 nextEf2,
      type_expr cenv Gamma nextSigma nextLeft nextEf1 ty ->
      type_expr cenv Gamma nextSigma nextRight nextEf2 ty ->
      type_expr cenv Gamma nextSigma (Prim (Bop op) [nextLeft; nextRight] rt)
        (nextEf1 ++ nextEf2) rt).
Proof.
  intros cenv Gamma Sigma op left right rt ef Htyped.
  inversion Htyped; subst.
  all: do 3 eexists;
    split; [reflexivity |]; split; [eassumption |]; split; [eassumption |];
    intros; econstructor; eauto.
Qed.

Lemma typed_binary_value_progress : forall ge p cenv Gamma Sigma vm m op first ta last tb rt ef,
  type_expr cenv Gamma Sigma (Prim (Bop op) [Val first ta; Val last tb] rt) ef rt ->
  exists v, ssem_expr ge p vm m (Prim (Bop op) [Val first ta; Val last tb] rt)
    m vm (Val v rt) /\ type_expr cenv Gamma Sigma (Val v rt) nil rt.
Proof.
  intros ge p cenv Gamma Sigma vm m op first ta last tb rt ef Htyped.
  destruct (binary_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Hef [Hfirst [Hlast Hrebuild]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hfirst) as Ha.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hlast) as Hb.
  simpl in Ha, Hb. subst ta tb.
  destruct op; inversion Htyped; subst.
  all: repeat match goal with
    H : type_expr _ _ _ (Val _ ?annotation) _ ?result |- _ =>
      first [constr_eq annotation result; fail 1 |
        let Heq := fresh "Heq" in
        pose proof (type_rel_typeof _ _ _ _ _ _ H) as Heq;
        cbn [typeof_expr] in Heq; subst]
    end.
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerAdd); exact Htyped].
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerSub); exact Htyped].
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerMul); exact Htyped].
  all: try solve [
    eapply typed_division_value_progress with (remainder := false); exact Htyped].
  all: try solve [
    eapply typed_division_value_progress with (remainder := true); exact Htyped].
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerAnd); exact Htyped].
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerOr); exact Htyped].
  all: try solve [
    eapply typed_total_integer_value_progress with (op := IntegerXor); exact Htyped].
  all: try solve [
    eapply typed_shift_value_progress with (rightshift := false); exact Htyped].
  all: try solve [
    eapply typed_shift_value_progress with (rightshift := true); exact Htyped].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Ceq); eauto].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Cne); eauto].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Clt); eauto].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Cgt); eauto].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Cle); eauto].
  all: try solve [
    eapply comparison_value_progress_from_types with (c := Cge); eauto].
Qed.

Lemma typed_binary_value_preservation :
  forall ge p cenv Gamma Sigma vm m op first ta last tb rt ef final vm' e',
  type_expr cenv Gamma Sigma (Prim (Bop op) [Val first ta; Val last tb] rt) ef rt ->
  ssem_expr ge p vm m (Prim (Bop op) [Val first ta; Val last tb] rt) final vm' e' ->
  final = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil rt.
Proof.
  intros ge p cenv Gamma Sigma vm m op first ta last tb rt ef final vm' e' Htyped Hstep.
  destruct (binary_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Hef [Hfirst [Hlast Hrebuild]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hfirst) as Ha.
  pose proof (type_rel_typeof _ _ _ _ _ _ Hlast) as Hb.
  simpl in Ha, Hb. subst ta tb.
  destruct op; inversion Htyped; subst.
  all: repeat match goal with
    H : type_expr _ _ _ (Val _ ?annotation) _ ?result |- _ =>
      first [constr_eq annotation result; fail 1 |
        let Heq := fresh "Heq" in
        pose proof (type_rel_typeof _ _ _ _ _ _ H) as Heq;
        cbn [typeof_expr] in Heq; subst]
    end.
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerAdd); eassumption].
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerSub); eassumption].
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerMul); eassumption].
  all: try solve [
    eapply typed_division_value_preservation with (remainder := false); eassumption].
  all: try solve [
    eapply typed_division_value_preservation with (remainder := true); eassumption].
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerAnd); eassumption].
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerOr); eassumption].
  all: try solve [
    eapply typed_total_integer_value_preservation with (op := IntegerXor); eassumption].
  all: try solve [
    eapply typed_shift_value_preservation with (rightshift := false); eassumption].
  all: try solve [
    eapply typed_shift_value_preservation with (rightshift := true); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Ceq); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Cne); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Clt); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Cgt); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Cle); eassumption].
  all: try solve [
    eapply comparison_value_preservation with (c := Cge); eassumption].
Qed.

Lemma binary_value_step_shape : forall ge p vm m op first ta last tb rt final vm' e',
  ssem_expr ge p vm m (Prim (Bop op) [Val first ta; Val last tb] rt) final vm' e' ->
  exists v, e' = Val v rt.
Proof.
  intros ge p vm m op first ta last tb rt final vm' e' Hstep.
  inversion Hstep; subst; eauto;
    exfalso; eapply value_has_no_small_step; eauto.
Qed.

Lemma typed_binary_result_primitive : forall cenv Gamma Sigma op left right rt ef,
  type_expr cenv Gamma Sigma (Prim (Bop op) [left; right] rt) ef rt ->
  exists pt, rt = Vtype pt.
Proof.
  intros cenv Gamma Sigma op left right rt ef Htyped.
  inversion Htyped; subst; eauto;
    destruct rt; simpl in *; try discriminate; eauto.
Qed.

Lemma primitive_value_configuration : forall ge Gamma Sigma vm m objects cells packets v pt ef,
  initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  type_expr ge.(genv_cenv) Gamma Sigma (Val v (Vtype pt)) ef (Vtype pt) ->
  coherent_layout cells ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v (Vtype pt)) ef (Vtype pt).
Proof.
  intros ge Gamma Sigma vm m objects cells packets v pt ef Hheap Htyped Hcoherent.
  split; [|exact Hcoherent]. constructor; auto.
  all: inversion Htyped; subst; simpl; exact I.
Qed.

Theorem coherent_binary_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p op first ta last tb rt ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Bop op) [Val first ta; Val last tb] rt) ef rt ->
  ssem_expr ge p vm m (Prim (Bop op) [Val first ta; Val last tb] rt) final vm' e' ->
  final = m /\ vm' = vm /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil rt.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op first ta last tb rt ef final vm' e'
    [[Hheap Htyped Hloc Hframes] Hcoherent] Hstep.
  destruct (typed_binary_value_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htyped Hstep)
    as [Hm [Hvm Hresult]].
  destruct (binary_value_step_shape _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as [v He].
  destruct (typed_binary_result_primitive _ _ _ _ _ _ _ _ Htyped) as [pt Hrt].
  subst final vm' e' rt. split; [reflexivity |]. split; [reflexivity |].
  apply primitive_value_configuration; assumption.
Qed.

Theorem coherent_binary_head_progress :
  forall ge Gamma Sigma vm m objects cells packets p op first ta last tb rt ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Bop op) [Val first ta; Val last tb] rt) ef rt ->
  exists v,
    ssem_expr ge p vm m (Prim (Bop op) [Val first ta; Val last tb] rt) m vm (Val v rt) /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v rt) nil rt.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op first ta last tb rt ef Hconfig.
  destruct (typed_binary_value_progress ge p ge.(genv_cenv) Gamma Sigma vm m op first ta last tb rt ef
    (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig))) as [v [Hstep Htyped]].
  exists v. split; [exact Hstep |].
  exact (proj2 (proj2 (coherent_binary_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfig Hstep))).
Qed.

Print Assumptions coherent_binary_head_progress.
Print Assumptions coherent_binary_head_preservation.

Theorem coherent_binary_preservation_from_operands :
  forall ge Gamma Sigma vm m objects cells packets p op left right rt ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Bop op) [left; right] rt) ef rt ->
  (forall operand effect ty,
    (operand = left \/ operand = right) ->
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand effect ty ->
    forall nextM nextVm next,
      ssem_expr ge p vm m operand nextM nextVm next ->
      exists Sigma' objects' cells' packets' effect',
        initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
        coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' ty /\
        sub_effect effect' effect = true) ->
  ssem_expr ge p vm m (Prim (Bop op) [left; right] rt) final vm' e' ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' e' ef' rt /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op left right rt ef final vm' e'
    Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [HleftLoc [HrightLoc _]] [HleftFrames [HrightFrames _]]] Hcoherent].
  destruct (binary_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Heffect [Hleft [Hright Hrebuild]]]]]]. subst ef.
  assert (HleftConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets left ef1 ty)
    by (split; [constructor; assumption | assumption]).
  assert (HrightConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets right ef2 ty)
    by (split; [constructor; assumption | assumption]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr ge p vm m left _ _ _ |- _ =>
      destruct (Hchild left ef1 ty (or_introl eq_refl) HleftConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
    destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (proj1 HrightConfig) Hupdate Hheap') as [_ Hright' HrightLoc' HrightFrames'].
    destruct Hnew as [_ Hleft' HleftLoc' HleftFrames'].
    exists Sigma', objects', cells', packets', (effect' ++ ef2). split; [exact Hupdate |]. split.
    + split; [constructor; simpl; auto | exact Hcoherent'].
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
  - match goal with Hs : ssem_expr ge p vm m right _ _ _ |- _ =>
      destruct (Hchild right ef2 ty (or_intror eq_refl) HrightConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hnew) as Hheap'.
    destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (proj1 HleftConfig) Hupdate Hheap') as [_ Hleft' HleftLoc' HleftFrames'].
    destruct Hnew as [_ Hright' HrightLoc' HrightFrames'].
    exists Sigma', objects', cells', packets', (ef1 ++ effect'). split; [exact Hupdate |]. split.
    + split; [constructor; simpl; auto | exact Hcoherent'].
    + apply sub_effect_concat; [apply sub_effect_refl | exact Hsub].
  all: destruct (coherent_binary_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hconfig Hstep) as [Hm [Hvm Hresult]];
    subst; exists Sigma, objects, cells, packets, nil;
    split; [eapply initialized_heap_evolution_refl; exact Hheap |];
    split; [exact Hresult | apply sub_effect_nil].
Qed.

Theorem coherent_binary_progress_from_operands :
  forall ge Gamma Sigma vm m objects cells packets p op left right rt ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Bop op) [left; right] rt) ef rt ->
  (forall operand effect ty,
    (operand = left \/ operand = right) ->
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand effect ty ->
    (exists v annotation, operand = Val v annotation) \/
      exists final vm' next, ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next,
    ssem_expr ge p vm m (Prim (Bop op) [left; right] rt) final vm' next.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op left right rt ef
    [[Hheap Htyped [HleftLoc [HrightLoc _]] [HleftFrames [HrightFrames _]]] Hcoherent] Hchild.
  destruct (binary_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Heffect [Hleft [Hright Hrebuild]]]]]].
  assert (HleftConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets left ef1 ty)
    by (split; [constructor; assumption | assumption]).
  assert (HrightConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets right ef2 ty)
    by (split; [constructor; assumption | assumption]).
  eapply binary_progress_from_operands;
    [exact Hleft | exact Hright | eapply Hchild; [left; reflexivity |exact HleftConfig] |
     eapply Hchild; [right; reflexivity |exact HrightConfig] |].
  intros first last Hone Htwo. subst left right.
  destruct (typed_binary_value_progress ge p ge.(genv_cenv) Gamma Sigma vm m op first ty last ty rt ef Htyped)
    as [v [Hstep Hresult]]. eauto.
Qed.

Print Assumptions coherent_binary_preservation_from_operands.
Print Assumptions coherent_binary_progress_from_operands.

Lemma typed_unary_result_primitive : forall cenv Gamma Sigma op operand ty ef,
  type_expr cenv Gamma Sigma (Prim (Uop op) [operand] ty) ef ty ->
  exists pt, ty = Vtype pt.
Proof.
  intros cenv Gamma Sigma op operand ty ef Htyped.
  inversion Htyped; subst; eauto;
    destruct ty; simpl in *; try discriminate; eauto.
Qed.

Theorem coherent_unary_head_preservation :
  forall ge Gamma Sigma vm m objects cells packets p op v ty ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Uop op) [Val v ty] ty) ef ty ->
  ssem_expr ge p vm m (Prim (Uop op) [Val v ty] ty) final vm' e' ->
  final = m /\ vm' = vm /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op v ty ef final vm' e'
    [[Hheap Htyped Hloc Hframes] Hcoherent] Hstep.
  destruct (typed_unary_value_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htyped Hstep)
    as [Hm [Hvm Hresult]].
  destruct (typed_unary_result_primitive _ _ _ _ _ _ _ Htyped) as [pt Hty].
  subst final vm' ty. split; [reflexivity |]. split; [reflexivity |].
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  apply primitive_value_configuration; assumption.
Qed.

Theorem coherent_unary_preservation_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p op operand ty ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Uop op) [operand] ty) ef ty ->
  (coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef ty ->
    forall nextM nextVm next,
      ssem_expr ge p vm m operand nextM nextVm next ->
      exists Sigma' objects' cells' packets' effect',
        initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
        coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' next effect' ty /\
        sub_effect effect' ef = true) ->
  ssem_expr ge p vm m (Prim (Uop op) [operand] ty) final vm' e' ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' e' ef' ty /\
    sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op operand ty ef final vm' e' Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent].
  destruct (unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hoperand Hrebuild].
  assert (HoperandConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef ty)
    by (split; [constructor; assumption | assumption]).
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr ge p vm m operand _ _ _ |- _ =>
      destruct (Hchild HoperandConfig _ _ _ Hs)
        as [Sigma' [objects' [cells' [packets' [effect' [Hupdate [[Hnew Hcoherent'] Hsub]]]]]]]
    end.
    destruct Hnew as [Hheap' Htyped' Hloc' Hframes'].
    exists Sigma', objects', cells', packets', effect'. split; [exact Hupdate |]. split; [|exact Hsub].
    split; [constructor; simpl; auto |exact Hcoherent'].
  - destruct (coherent_unary_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hconfig Hstep) as [Hm [Hvm Hresult]].
    subst. exists Sigma, objects, cells, packets, nil.
    split; [eapply initialized_heap_evolution_refl; exact Hheap |].
    split; [exact Hresult |apply sub_effect_nil].
Qed.

Theorem coherent_unary_progress_from_operand :
  forall ge Gamma Sigma vm m objects cells packets p op operand ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (Uop op) [operand] ty) ef ty ->
  (coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef ty ->
    (exists v annotation, operand = Val v annotation) \/
      exists final vm' next, ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next,
    ssem_expr ge p vm m (Prim (Uop op) [operand] ty) final vm' next.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p op operand ty ef
    [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent] Hchild.
  destruct (unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hoperand Hrebuild].
  eapply unary_progress_from_operand; [exact Htyped |].
  apply Hchild. split; [constructor; assumption |exact Hcoherent].
Qed.

Print Assumptions coherent_unary_head_preservation.
Print Assumptions coherent_unary_preservation_from_operand.
Print Assumptions coherent_unary_progress_from_operand.
