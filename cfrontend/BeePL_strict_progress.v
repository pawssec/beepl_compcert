(* Evaluated argument lists are summaries, not expression computation steps.
   Guarded contexts must expose an actual nonvalue expression step; evaluated
   application/initializer heads can no longer use list identity as progress. *)
Require Import List Bool Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_soundness_memory.
Import ListNotations.

Lemma all_value_arguments_is_values : forall es,
  Forall (fun e => exists v ty, e = Val v ty) es -> is_values es = true.
Proof.
  intros es Hvalues. induction Hvalues; [reflexivity |].
  destruct H as [v [ty He]]. subst x. simpl. exact IHHvalues.
Qed.

Lemma is_values_all_value_arguments : forall es,
  is_values es = true -> Forall (fun e => exists v ty, e = Val v ty) es.
Proof.
  induction es as [|e es IH]; intros Hvalues; [constructor |].
  simpl in Hvalues. apply andb_true_iff in Hvalues. destruct Hvalues as [Hhead Htail].
  constructor; [destruct e; try discriminate; do 2 eexists; reflexivity |apply IH; exact Htail].
Qed.

Lemma stepping_expression_is_not_value : forall ge p vm m e final vm' e',
  ssem_expr ge p vm m e final vm' e' -> is_value e = false.
Proof.
  intros ge p vm m e final vm' e' Hstep. destruct e; try reflexivity.
  exfalso. eapply value_has_no_small_step; eauto.
Qed.

Theorem guarded_list_step_exposes_expression : forall ge p vm m es final vm' es',
  ssem_exprs ge p vm m es final vm' es' -> is_values es = false ->
  exists prefix active suffix next,
    Forall (fun e => exists v ty, e = Val v ty) prefix /\
    es = prefix ++ active :: suffix /\ es' = prefix ++ next :: suffix /\
    is_value active = false /\ ssem_expr ge p vm m active final vm' next.
Proof.
  intros ge p vm m es final vm' es' Hstep. induction Hstep; intros Hnonvalues.
  - discriminate Hnonvalues.
  - exists [], e, es, e'. split; [constructor |].
    split; [reflexivity |]. split; [reflexivity |].
    split; [eapply stepping_expression_is_not_value; eauto |assumption].
  - simpl in Hnonvalues.
    destruct (IHHstep Hnonvalues) as [prefix [active [suffix [next [Hprefix [Hes [Hnext [Hactive Hrun]]]]]]]].
    exists (Val v t :: prefix), active, suffix, next.
    split; [constructor; [do 2 eexists; reflexivity |exact Hprefix] |].
    split; [simpl; f_equal; exact Hes |]. split; [simpl; f_equal; exact Hnext |]. split; assumption.
Qed.

Theorem evaluated_application_step_is_frame :
  forall ge p vm m fn annotation es result final vm' e',
  Forall (fun e => exists v ty, e = Val v ty) es ->
  ssem_expr ge p vm m (App (Val fn annotation) es result) final vm' e' ->
  exists callee body, e' = CallFrame callee body result.
Proof.
  intros ge p vm m fn annotation es result final vm' e' Hvalues Hstep.
  pose proof (all_value_arguments_is_values es Hvalues) as Hready.
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try congruence; do 2 eexists; reflexivity.
Qed.

Theorem evaluated_array_initializer_step_is_value :
  forall ge p vm m arr ty es final vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Ainit arr ty es ty) final vm' e' ->
  exists fresh, e' = Val (Vloc fresh Ptrofs.zero) ty.
Proof.
  intros ge p vm m arr ty es final vm' e' Hvalues Hstep.
  inversion Hstep; subst.
  - inversion Hvalues as [|head tail Hhead Htail]; subst. destruct Hhead as [v [t He]]. subst e.
    exfalso. eapply value_has_no_small_step; eauto.
  - inversion Hvalues as [|head tail Hhead Htail]; subst.
    pose proof (all_value_arguments_is_values _ Htail) as Hready. congruence.
  - eexists; reflexivity.
Qed.

Theorem evaluated_structure_initializer_step_is_value :
  forall ge p vm m sid ids es ty final vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Sinit sid ids es ty) final vm' e' ->
  exists fresh, e' = Val (Vloc fresh Ptrofs.zero) ty.
Proof.
  intros ge p vm m sid ids es ty final vm' e' Hvalues Hstep.
  pose proof (all_value_arguments_is_values es Hvalues) as Hready.
  inversion Hstep; subst; try congruence. eexists; reflexivity.
Qed.

Corollary evaluated_application_cannot_stutter :
  forall ge p vm m fn annotation es result final vm' e',
  Forall (fun e => exists v ty, e = Val v ty) es ->
  ssem_expr ge p vm m (App (Val fn annotation) es result) final vm' e' ->
  e' <> App (Val fn annotation) es result.
Proof. intros. edestruct evaluated_application_step_is_frame as [callee [body He]]; eauto. subst e'; discriminate. Qed.

Corollary evaluated_array_initializer_cannot_stutter :
  forall ge p vm m arr ty es final vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Ainit arr ty es ty) final vm' e' -> e' <> Ainit arr ty es ty.
Proof. intros. edestruct evaluated_array_initializer_step_is_value as [fresh He]; eauto. subst e'; discriminate. Qed.

Corollary evaluated_structure_initializer_cannot_stutter :
  forall ge p vm m sid ids es ty final vm' e',
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Sinit sid ids es ty) final vm' e' -> e' <> Sinit sid ids es ty.
Proof. intros. edestruct evaluated_structure_initializer_step_is_value as [fresh He]; eauto. subst e'; discriminate. Qed.

Print Assumptions guarded_list_step_exposes_expression.
Print Assumptions evaluated_application_cannot_stutter.
Print Assumptions evaluated_array_initializer_cannot_stutter.
Print Assumptions evaluated_structure_initializer_cannot_stutter.
