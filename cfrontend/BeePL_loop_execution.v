(* Finite unit-valued executions validate the incremental loop machinery.
   Completion evidence is used only to relate terminating runs; entering a
   loop has no such premise. The legacy summary accepts arbitrary terminal
   body values, so its untyped converse would not be a valid theorem. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_loop_proofs.
Local Open Scope nat_scope.

Lemma loop_closure_prepend : forall ge p vm m e nextM nextVm next steps final finalVm result,
  ssem_expr ge p vm m e nextM nextVm next ->
  ssem_closure ge p nextVm nextM next steps final finalVm result ->
  ssem_closure ge p vm m e (S steps) final finalVm result.
Proof. intros. rewrite <- (ssrnat.addn1 steps). eapply ssem_multi; eauto. Qed.

Definition incremental_loop_start (count : nat) (body : expr) : expr :=
  match count with O => Val Vunit Utype | S remaining => LoopFrame remaining body body end.

Lemma loop_frame_closure_then :
  forall ge p vm m active steps nextM nextVm endpoint,
  ssem_closure ge p vm m active steps nextM nextVm endpoint ->
  forall remaining template after final finalVm result,
  ssem_closure ge p nextVm nextM (LoopFrame remaining template endpoint) after final finalVm result ->
  ssem_closure ge p vm m (LoopFrame remaining template active) (steps + after) final finalVm result.
Proof.
  intros ge p vm m active steps nextM nextVm endpoint Hrun.
  induction Hrun; intros remaining template after final finalVm result Hafter.
  - exact Hafter.
  - replace (1 + after) with (S after) by lia.
    eapply loop_closure_prepend; [apply ssem_loop_frame_step; eassumption |exact Hafter].
  - rewrite ssrnat.addn1. replace (S n + after) with (S (n + after)) by lia.
    eapply loop_closure_prepend; [apply ssem_loop_frame_step; eassumption |].
    eapply IHHrun; exact Hafter.
Qed.

Lemma completed_loop_frame_advances : forall ge p vm m remaining body,
  ssem_expr ge p vm m (LoopFrame remaining body (Val Vunit Utype))
    m vm (incremental_loop_start remaining body).
Proof. intros. destruct remaining; constructor. Qed.

Inductive completed_unit_iterations (ge : genv) (p : program) (body : expr) :
    nat -> vmap -> Mem.mem -> Mem.mem -> vmap -> Prop :=
| unit_iterations_nil : forall vm m,
    completed_unit_iterations ge p body O vm m m vm
| unit_iterations_cons : forall remaining vm m nextM nextVm final finalVm steps,
    ssem_closure ge p vm m body steps nextM nextVm (Val Vunit Utype) ->
    completed_unit_iterations ge p body remaining nextVm nextM final finalVm ->
    completed_unit_iterations ge p body (S remaining) vm m final finalVm.

Theorem completed_unit_iterations_summary :
  forall ge p body count vm m final finalVm,
  completed_unit_iterations ge p body count vm m final finalVm ->
  ssem_bfor ge p (Z.of_nat count) vm m body final finalVm (Val Vunit Utype).
Proof.
  intros ge p body count vm m final finalVm Hiterations. induction Hiterations.
  - constructor.
  - eapply ssem_for_one; [|exact IHHiterations].
    eapply completed_evaluation_loop_body; eauto.
Qed.

Theorem completed_unit_iterations_incremental :
  forall ge p body count vm m final finalVm,
  completed_unit_iterations ge p body count vm m final finalVm ->
  exists steps,
    ssem_closure ge p vm m (incremental_loop_start count body) steps final finalVm (Val Vunit Utype).
Proof.
  intros ge p body count vm m final finalVm Hiterations. induction Hiterations.
  - exists O. constructor.
  - destruct IHHiterations as [tailSteps Htail].
    exists (steps + S tailSteps). simpl.
    eapply loop_frame_closure_then; [eassumption |].
    eapply loop_closure_prepend; [apply completed_loop_frame_advances |exact Htail].
Qed.

Theorem completed_unit_source_loop_execution :
  forall ge p vm m body first firstTy last lastTy direction count final finalVm,
  compute_loop_iterations direction firstTy first last = OK count ->
  completed_unit_iterations ge p body (Z.to_nat count) vm m final finalVm ->
  exists steps,
    ssem_closure ge p vm m
      (For (Val first firstTy) (Val last lastTy) direction body Utype)
      steps final finalVm (Val Vunit Utype).
Proof.
  intros ge p vm m body first firstTy last lastTy direction count final finalVm Hcount Hiterations.
  destruct (completed_unit_iterations_incremental _ _ _ _ _ _ _ _ Hiterations) as [steps Hrun].
  exists (S steps). eapply loop_closure_prepend; [|exact Hrun].
  apply ssem_for3. exact Hcount.
Qed.

(* An existing terminating summary can also be replayed incrementally if its
   individual body completions are unit-valued. No new termination witness is
   required at loop entry. *)
Theorem unit_body_summary_replays :
  forall ge p body,
  (forall vm m final finalVm,
    ssem_loop_body ge p vm m body final finalVm ->
    exists steps, ssem_closure ge p vm m body steps final finalVm (Val Vunit Utype)) ->
  forall count vm m final finalVm result,
  ssem_bfor ge p count vm m body final finalVm result ->
  completed_unit_iterations ge p body (Z.to_nat count) vm m final finalVm.
Proof.
  intros ge p body Hunit count vm m final finalVm result Hsummary.
  induction Hsummary.
  - constructor.
  - destruct (Hunit _ _ _ _ H) as [steps Hrun].
    rewrite Nat2Z.id in *. eapply unit_iterations_cons; eauto.
Qed.

Print Assumptions loop_frame_closure_then.
Print Assumptions completed_unit_iterations_summary.
Print Assumptions completed_unit_iterations_incremental.
Print Assumptions completed_unit_source_loop_execution.
Print Assumptions unit_body_summary_replays.
