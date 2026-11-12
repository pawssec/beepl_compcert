(* Small steps preserve the surrounding variable map. Callee maps are captured
   inside CallFrame, so entering or stepping a call does not change this fact. *)
Require Import BeePL BeePL_sem.

Scheme environment_expr_ind := Induction for ssem_expr Sort Prop
  with environment_exprs_ind := Induction for ssem_exprs Sort Prop
  with environment_for_ind := Induction for ssem_bfor Sort Prop
  with environment_body_ind := Induction for ssem_loop_body Sort Prop.
Combined Scheme environment_steps_ind from environment_expr_ind,
  environment_exprs_ind, environment_for_ind, environment_body_ind.

Theorem small_steps_preserve_environment : forall bge,
  (forall p vm m e m' vm' e', ssem_expr bge p vm m e m' vm' e' -> vm' = vm) /\
  (forall p vm m es m' vm' es', ssem_exprs bge p vm m es m' vm' es' -> vm' = vm) /\
  (forall p n vm m body m' vm' result,
    ssem_bfor bge p n vm m body m' vm' result -> vm' = vm) /\
  (forall p vm m body m' vm', ssem_loop_body bge p vm m body m' vm' -> vm' = vm).
Proof.
  intro bge. apply environment_steps_ind; intros; congruence.
Qed.

Corollary expression_step_preserves_environment : forall bge p vm m e m' vm' e',
  ssem_expr bge p vm m e m' vm' e' -> vm' = vm.
Proof. intros; eapply (proj1 (small_steps_preserve_environment bge)); eauto. Qed.

Corollary arguments_step_preserves_environment : forall bge p vm m es m' vm' es',
  ssem_exprs bge p vm m es m' vm' es' -> vm' = vm.
Proof. intros; eapply (proj1 (proj2 (small_steps_preserve_environment bge))); eauto. Qed.

Corollary loop_execution_preserves_environment : forall bge p n vm m body m' vm' result,
  ssem_bfor bge p n vm m body m' vm' result -> vm' = vm.
Proof. intros; eapply (proj1 (proj2 (proj2 (small_steps_preserve_environment bge)))); eauto. Qed.

Corollary loop_body_preserves_environment : forall bge p vm m body m' vm',
  ssem_loop_body bge p vm m body m' vm' -> vm' = vm.
Proof. intros; eapply (proj2 (proj2 (proj2 (small_steps_preserve_environment bge)))); eauto. Qed.

Theorem expression_closure_preserves_environment : forall bge p vm m e n m' vm' e',
  ssem_closure bge p vm m e n m' vm' e' -> vm' = vm.
Proof.
  intros bge p vm m e n m' vm' e' Hclosure. induction Hclosure.
  - reflexivity.
  - eapply expression_step_preserves_environment; eauto.
  - rewrite IHHclosure. eapply expression_step_preserves_environment; eauto.
Qed.

Theorem arguments_closure_preserves_environment : forall bge p vm m es n m' vm' es',
  ssem_closures bge p vm m es n m' vm' es' -> vm' = vm.
Proof.
  intros bge p vm m es n m' vm' es' Hclosure. induction Hclosure.
  - eapply arguments_step_preserves_environment; eauto.
  - rewrite IHHclosure. eapply arguments_step_preserves_environment; eauto.
Qed.

Print Assumptions small_steps_preserve_environment.
Print Assumptions expression_closure_preserves_environment.
Print Assumptions arguments_closure_preserves_environment.
