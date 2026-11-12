(* Loop-bound contexts derive the retained disjointness condition from actual
   typed-step free-variable nonincrease; no post-step disjointness is assumed. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_substitution_freevars BeePL_step_freevars.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations.
Import ListNotations.

Lemma for_typing_effect_components : forall env Gamma Sigma first last d body ty ef,
  type_expr env Gamma Sigma (For first last d body ty) ef ty ->
  exists t1 t2 e1 e2 eb, ty=Utype /\ ef=e1++e2++eb /\
    type_expr env Gamma Sigma first e1 t1 /\ type_expr env Gamma Sigma last e2 t2 /\
    type_expr env Gamma Sigma body eb Utype /\
    eq_type t1 t2=true /\ (is_primint t1 || is_primlong t1)=true /\
    disjoint_vars(free_variables body)(free_variables first)=true /\
    disjoint_vars(free_variables body)(free_variables last)=true.
Proof. intros * H; inversion H; subst. do 5 eexists; repeat split; eauto. Qed.

Theorem coherent_for_first_context : forall ge Gamma Sigma vm m objects cells packets p first last d body ty ef final vm' first',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (For first last d body ty) ef ty ->
  ssem_expr ge p vm m first final vm' first' ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets first effect boundType ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' first' effect' boundType /\
      sub_effect effect' effect=true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (For first last d body ty) final vm' (For first' last d body ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' (For first' last d body ty) ef' ty /\
    sub_effect ef' ef=true.
Proof.
  intros * [[Hheap Htyped [Hfloc [Hlloc Hbloc]] [Hfframes [Hlframes Hbframes]]] Hcoherent] Hstep Hchild.
  destruct (for_typing_effect_components _ _ _ _ _ _ _ _ _ Htyped)
    as [t1 [t2 [e1 [e2 [eb [Hty [Hef [Hfirst [Hlast [Hbody [Heq [Hint [Hd1 Hd2]]]]]]]]]]]]].
  subst ty ef.
  assert (HfirstConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets first e1 t1)
    by (split; [constructor; assumption|exact Hcoherent]).
  destruct (Hchild _ _ HfirstConfig) as [Sigma' [objects' [cells' [packets' [e1' [Hevolve [[[Hheap' Hfirst' Hfloc' Hfframes'] Hcoherent'] Hsub]]]]]]].
  assert (HlastConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets last e2 t2)
    by (constructor; assumption).
  assert (HbodyConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets body eb Utype)
    by (constructor; assumption).
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HlastConfig Hevolve Hheap') as [_ Hlast' Hlloc' Hlframes'].
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HbodyConfig Hevolve Hheap') as [_ Hbody' Hbloc' Hbframes'].
  exists Sigma', objects', cells', packets', (e1'++e2++eb).
  split; [apply ssem_for1; exact Hstep|]. split; [exact Hevolve|]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto.
    eapply ty_for; eauto.
    eapply disjoint_vars_incl; [apply incl_refl|eapply typed_step_free_variables; eauto|exact Hd1].
  - apply sub_effect_concat; [exact Hsub|apply sub_effect_refl].
Qed.

Theorem coherent_for_last_context : forall ge Gamma Sigma vm m objects cells packets p value annotation last d body ty ef final vm' last',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (For (Val value annotation) last d body ty) ef ty ->
  ssem_expr ge p vm m last final vm' last' ->
  (forall effect boundType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets last effect boundType ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' last' effect' boundType /\
      sub_effect effect' effect=true) ->
  exists Sigma' objects' cells' packets' ef',
    ssem_expr ge p vm m (For (Val value annotation) last d body ty) final vm' (For (Val value annotation) last' d body ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' (For (Val value annotation) last' d body ty) ef' ty /\
    sub_effect ef' ef=true.
Proof.
  intros * [[Hheap Htyped [Hfloc [Hlloc Hbloc]] [Hfframes [Hlframes Hbframes]]] Hcoherent] Hstep Hchild.
  destruct (for_typing_effect_components _ _ _ _ _ _ _ _ _ Htyped)
    as [t1 [t2 [e1 [e2 [eb [Hty [Hef [Hfirst [Hlast [Hbody [Heq [Hint [Hd1 Hd2]]]]]]]]]]]]].
  subst ty ef.
  assert (HlastConfig : coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets last e2 t2)
    by (split; [constructor; assumption|exact Hcoherent]).
  destruct (Hchild _ _ HlastConfig) as [Sigma' [objects' [cells' [packets' [e2' [Hevolve [[[Hheap' Hlast' Hlloc' Hlframes'] Hcoherent'] Hsub]]]]]]].
  assert (HfirstConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val value annotation) e1 t1)
    by (constructor; assumption).
  assert (HbodyConfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets body eb Utype)
    by (constructor; assumption).
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HfirstConfig Hevolve Hheap') as [_ Hfirst' Hfloc' Hfframes'].
  destruct (initialized_configuration_reframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HbodyConfig Hevolve Hheap') as [_ Hbody' Hbloc' Hbframes'].
  exists Sigma', objects', cells', packets', (e1++e2'++eb).
  split; [apply ssem_for2; exact Hstep|]. split; [exact Hevolve|]. split.
  - split; [|exact Hcoherent']. constructor; simpl; auto.
    eapply ty_for; eauto.
    eapply disjoint_vars_incl; [apply incl_refl|eapply typed_step_free_variables; eauto|exact Hd2].
  - apply sub_effect_concat; [apply sub_effect_refl|]. apply sub_effect_concat; [exact Hsub|apply sub_effect_refl].
Qed.
Print Assumptions coherent_for_first_context.
Print Assumptions coherent_for_last_context.
