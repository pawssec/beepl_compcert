(* Loop counts and execution, without admitted BeePL proof dependencies. *)
Require Import List ZArith Lia Integers AST Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Import ListNotations.
Local Open Scope Z_scope.

Lemma inclusive_loop_iterations_nonnegative : forall d first last,
  0 <= inclusive_loop_iterations d first last.
Proof. intros; unfold inclusive_loop_iterations; apply Z.le_max_l. Qed.

Lemma compute_loop_iterations_nonnegative : forall d ty first last n,
  compute_loop_iterations d ty first last = OK n -> 0 <= n.
Proof.
  intros d ty first last n Hcount. unfold compute_loop_iterations in Hcount.
  destruct (loop_integer_value ty first); try discriminate.
  destruct (loop_integer_value ty last); try discriminate.
  inversion Hcount; subst. apply inclusive_loop_iterations_nonnegative.
Qed.

Lemma ascending_inclusive_count : forall first last,
  first <= last -> inclusive_loop_iterations Up first last = last - first + 1.
Proof. intros; unfold inclusive_loop_iterations; apply Z.max_r; lia. Qed.

Lemma descending_inclusive_count : forall first last,
  last <= first -> inclusive_loop_iterations Down first last = first - last + 1.
Proof. intros; unfold inclusive_loop_iterations; apply Z.max_r; lia. Qed.

Lemma ascending_empty_count : forall first last,
  last < first -> inclusive_loop_iterations Up first last = 0.
Proof. intros; unfold inclusive_loop_iterations; apply Z.max_l; lia. Qed.

Lemma descending_empty_count : forall first last,
  first < last -> inclusive_loop_iterations Down first last = 0.
Proof. intros; unfold inclusive_loop_iterations; apply Z.max_l; lia. Qed.

Lemma int32_loop_count_regressions :
  compute_loop_iterations Up (Vtype (Tint I32 Signed noattr))
    (Vint (Int.repr 0)) (Vint (Int.repr 3)) = OK 4 /\
  compute_loop_iterations Down (Vtype (Tint I32 Signed noattr))
    (Vint (Int.repr 3)) (Vint (Int.repr 0)) = OK 4 /\
  compute_loop_iterations Up (Vtype (Tint I32 Signed noattr))
    (Vint (Int.repr 3)) (Vint (Int.repr 0)) = OK 0 /\
  compute_loop_iterations Up (Vtype (Tint I32 Signed noattr))
    (Vint (Int.repr (-2))) (Vint (Int.repr 1)) = OK 4 /\
  compute_loop_iterations Up (Vtype (Tint I32 Unsigned noattr))
    (Vint Int.mone) (Vint Int.mone) = OK 1.
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma big_step_loop_result_unit : forall bge p n vm m body m' vm' v,
  bsem_bfor bge p n vm m body m' vm' v -> v = Vunit.
Proof. intros bge p n vm m body m' vm' v Hrun; induction Hrun; auto. Qed.

Lemma small_step_loop_result_unit : forall bge p n vm m body m' vm' e,
  ssem_bfor bge p n vm m body m' vm' e -> e = Val Vunit Utype.
Proof. intros bge p n vm m body m' vm' e Hrun; induction Hrun; auto. Qed.

Lemma loop_body_one_step : forall bge p vm m body m' vm' v ty,
  ssem_expr bge p vm m body m' vm' (Val v ty) ->
  ssem_loop_body bge p vm m body m' vm'.
Proof. intros; eapply ssem_loop_body_step; [eassumption | constructor]. Qed.

Lemma repeat_unit_body : forall n bge p vm m,
  ssem_bfor bge p (Z.of_nat n) vm m (Unit Utype) m vm (Val Vunit Utype).
Proof.
  induction n; intros.
  - constructor.
  - eapply ssem_for_one; [eapply loop_body_one_step; apply ssem_ut | apply IHn].
Qed.

Lemma unit_loop_frame_completes : forall remaining bge p vm m,
  ssem_closure bge p vm m (LoopFrame remaining (Unit Utype) (Unit Utype))
    (2 * S remaining)%nat m vm (Val Vunit Utype).
Proof.
  induction remaining; intros.
  - change (ssem_closure bge p vm m (LoopFrame O (Unit Utype) (Unit Utype))
      (1 + 1)%nat m vm (Val Vunit Utype)).
    eapply ssem_multi; [apply ssem_loop_frame_step; apply ssem_ut |].
    apply ssem_one. apply ssem_loop_frame_done.
  - replace (2 * S (S remaining))%nat with ((2 * S remaining + 1) + 1)%nat by lia.
    eapply ssem_multi; [apply ssem_loop_frame_step; apply ssem_ut |].
    eapply ssem_multi; [apply ssem_loop_frame_restart |]. apply IHremaining.
Qed.

(* Four iterations now expose nine source transitions rather than hiding all
   body execution inside a single purported small step. *)
Lemma ascending_loop_executes_body : forall bge p vm m,
  ssem_closure bge p vm m
    (For (Val (Vint (Int.repr 0)) (Vtype (Tint I32 Signed noattr)))
      (Val (Vint (Int.repr 3)) (Vtype (Tint I32 Signed noattr))) Up (Unit Utype) Utype)
    9%nat m vm (Val Vunit Utype).
Proof.
  intros. change (ssem_closure bge p vm m
    (For (Val (Vint (Int.repr 0)) (Vtype (Tint I32 Signed noattr)))
      (Val (Vint (Int.repr 3)) (Vtype (Tint I32 Signed noattr))) Up (Unit Utype) Utype)
    (8 + 1)%nat m vm (Val Vunit Utype)).
  eapply ssem_multi with (e' := LoopFrame 3 (Unit Utype) (Unit Utype)).
  - apply ssem_for3 with (n := 4). vm_compute; reflexivity.
  - exact (unit_loop_frame_completes 3 bge p vm m).
Qed.

Lemma evaluated_loop_enters_without_body_completion :
  forall bge p vm m body count first firstTy last lastTy direction,
  compute_loop_iterations direction firstTy first last = OK count ->
  ssem_expr bge p vm m (For (Val first firstTy) (Val last lastTy) direction body Utype)
    m vm (match Z.to_nat count with
          | O => Val Vunit Utype
          | S remaining => LoopFrame remaining body body
          end).
Proof. intros; eapply ssem_for3; eauto. Qed.

Print Assumptions compute_loop_iterations_nonnegative.
Print Assumptions int32_loop_count_regressions.
Print Assumptions big_step_loop_result_unit.
Print Assumptions small_step_loop_result_unit.
Print Assumptions ascending_loop_executes_body.

Lemma unit_body_loop_typable : forall cenv Gamma Sigma first last d,
  type_expr cenv Gamma Sigma
    (For (Val (Vint first) (Vtype (Tint I32 Signed noattr)))
      (Val (Vint last) (Vtype (Tint I32 Signed noattr))) d (Unit Utype) Utype) nil Utype.
Proof.
  intros. eapply ty_for with (ef1 := nil) (ef2 := nil) (ef := nil)
    (t1 := Vtype (Tint I32 Signed noattr)) (t2 := Vtype (Tint I32 Signed noattr))
    (fv1 := nil) (fv2 := nil) (fv := nil);
    try apply ty_vali; try apply ty_unit; reflexivity.
Qed.

Lemma typed_loop_result_unit : forall cenv Gamma Sigma low high d body annotation ef result,
  type_expr cenv Gamma Sigma (For low high d body annotation) ef result -> result = Utype.
Proof. intros; inversion H; subst; reflexivity. Qed.

Print Assumptions unit_body_loop_typable.
Print Assumptions typed_loop_result_unit.

Lemma primitive_loop_bounds_total : forall d pt first last,
  typeof_value first (Vtype pt) -> typeof_value last (Vtype pt) ->
  (is_primint (Vtype pt) || is_primlong (Vtype pt))%bool = true ->
  exists n, compute_loop_iterations d (Vtype pt) first last = OK n /\ 0 <= n.
Proof.
  intros d pt first last Hfirst Hlast Hnumeric.
  destruct pt; destruct first; destruct last;
    simpl in Hfirst, Hlast, Hnumeric; try contradiction; try discriminate.
  all: eexists; split; [reflexivity | apply inclusive_loop_iterations_nonnegative].
Qed.

Print Assumptions primitive_loop_bounds_total.

Lemma loop_body_completed_evaluation : forall bge p vm m body m' vm',
  ssem_loop_body bge p vm m body m' vm' ->
  exists v ty steps, ssem_closure bge p vm m body steps m' vm' (Val v ty).
Proof.
  intros bge p vm m body m' vm' Hbody. induction Hbody.
  - exists v, t, O. constructor.
  - destruct IHHbody as [v [ty [steps Hclosure]]].
    exists v, ty, (steps + 1)%nat. eapply ssem_multi; eauto.
Qed.

Lemma completed_evaluation_loop_body : forall bge p vm m body steps m' vm' result,
  ssem_closure bge p vm m body steps m' vm' result ->
  forall v ty, result = Val v ty -> ssem_loop_body bge p vm m body m' vm'.
Proof.
  intros bge p vm m body steps m' vm' result Hclosure.
  induction Hclosure; intros v0 ty Heq; subst.
  - constructor.
  - eapply loop_body_one_step; eassumption.
  - eapply ssem_loop_body_step; [eassumption |]. eapply IHHclosure; reflexivity.
Qed.

Theorem loop_body_completion_iff : forall bge p vm m body m' vm',
  ssem_loop_body bge p vm m body m' vm' <->
  exists v ty steps, ssem_closure bge p vm m body steps m' vm' (Val v ty).
Proof.
  intros; split; [apply loop_body_completed_evaluation |].
  intros [v [ty [steps Hclosure]]]. eapply completed_evaluation_loop_body; eauto.
Qed.

Theorem loop_repetition_preserves_state :
  forall (Q : vmap -> Memory.mem -> Prop) bge p body,
  (forall vm m vm' m', Q vm m -> ssem_loop_body bge p vm m body m' vm' -> Q vm' m') ->
  forall n vm m vm' m' result,
  ssem_bfor bge p n vm m body m' vm' result -> Q vm m -> Q vm' m'.
Proof.
  intros Q bge p body Hbody n vm m vm' m' result Hrun.
  induction Hrun; intro Hstate; [exact Hstate |].
  apply IHHrun; [exact Hbody |]. eapply Hbody; eauto.
Qed.

Theorem loop_repetition_exists :
  forall (Q : vmap -> Memory.mem -> Prop) bge p body,
  (forall vm m, Q vm m -> exists vm' m',
    ssem_loop_body bge p vm m body m' vm' /\ Q vm' m') ->
  forall count vm m, Q vm m ->
  exists vm' m', ssem_bfor bge p (Z.of_nat count) vm m body m' vm' (Val Vunit Utype) /\ Q vm' m'.
Proof.
  intros Q bge p body Hbody count. induction count; intros vm m Hstate.
  - exists vm, m. split; [constructor | exact Hstate].
  - destruct (Hbody vm m Hstate) as [next_vm [next_m [Hiteration Hstate']]].
    destruct (IHcount next_vm next_m Hstate') as [final_vm [final_m [Hrest Hfinal]]].
    exists final_vm, final_m. split; [eapply ssem_for_one; eauto | exact Hfinal].
Qed.

Print Assumptions loop_body_completion_iff.
Print Assumptions loop_repetition_preserves_state.
Print Assumptions loop_repetition_exists.
