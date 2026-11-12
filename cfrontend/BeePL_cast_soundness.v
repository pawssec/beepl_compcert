(* Primitive casts preserve their declared target type. Boolean targets use
   target-directed decoding rather than exposing their integer representation. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Cop Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory.
Import ListNotations.

Lemma allowed_cast_target : forall source target result,
  allowed_cast source target = OK result -> result = target.
Proof. destruct source; destruct target; simpl; intros; congruence. Qed.

Theorem typed_primitive_cast_total : forall cenv Gamma Sigma v source target ef m,
  type_expr cenv Gamma Sigma (Val v (Vtype source)) ef (Vtype source) ->
  allowed_cast source target = OK target ->
  exists cv result,
    Cop.sem_cast (trans_bvalue_cvalue v) (transBeePL_type (Vtype source))
      (transBeePL_type (Vtype target)) m = Some cv /\
    decode_memory_value (Vtype target) cv = OK result /\
    type_expr cenv Gamma Sigma (Val result (Vtype target)) nil (Vtype target).
Proof.
  intros cenv Gamma Sigma v source target ef m Htyped Hallowed.
  inversion Htyped; subst; destruct target; simpl in Hallowed; try discriminate;
    cbn [Cop.sem_cast Cop.classify_cast decode_memory_value transBeePL_type trans_bvalue_cvalue trans_cvalue_bvalue];
    repeat match goal with sz : intsize |- _ => destruct sz | b : bool |- _ => destruct b | sg : signedness |- _ => destruct sg end;
    cbn [Cop.sem_cast Cop.classify_cast decode_memory_value transBeePL_type trans_bvalue_cvalue trans_cvalue_bvalue];
    repeat eexists; repeat split; try reflexivity; constructor.
Qed.

Theorem primitive_cast_value_progress : forall ge p vm m Gamma Sigma v source target ef,
  type_expr ge.(genv_cenv) Gamma Sigma (Val v (Vtype source)) ef (Vtype source) ->
  allowed_cast source target = OK target ->
  exists result,
    ssem_expr ge p vm m
      (Prim (Cast (Vtype target)) [Val v (Vtype source)] (Vtype target))
      m vm (Val result (Vtype target)) /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val result (Vtype target)) nil (Vtype target).
Proof.
  intros ge p vm m Gamma Sigma v source target ef Htyped Hallowed.
  destruct (typed_primitive_cast_total _ _ _ _ _ _ _ m Htyped Hallowed)
    as [cv [result [Hcast [Hdecode Hresult]]]].
  exists result. split; [eapply ssem_cast2; eauto|exact Hresult].
Qed.

Theorem primitive_cast_value_preservation :
  forall ge p vm m Gamma Sigma v source target ef m' vm' e',
  type_expr ge.(genv_cenv) Gamma Sigma (Val v (Vtype source)) ef (Vtype source) ->
  allowed_cast source target = OK target ->
  ssem_expr ge p vm m
    (Prim (Cast (Vtype target)) [Val v (Vtype source)] (Vtype target)) m' vm' e' ->
  m' = m /\ vm' = vm /\ exists result,
    e' = Val result (Vtype target) /\
    type_expr ge.(genv_cenv) Gamma Sigma e' nil (Vtype target).
Proof.
  intros ge p vm m Gamma Sigma v source target ef m' vm' e' Htyped Hallowed Hstep.
  destruct (typed_primitive_cast_total _ _ _ _ _ _ _ m Htyped Hallowed)
    as [cv [result [Hcast [Hdecode Hresult]]]].
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - assert (v' = cv) by congruence. subst v'.
    assert (v'' = result) by congruence. subst v''.
    split; [reflexivity|]. split; [reflexivity|]. exists result; auto.
Qed.

Print Assumptions typed_primitive_cast_total.
Print Assumptions primitive_cast_value_preservation.

(* BeePL Bool currently lowers to uint8, not C _Bool: cast truncation precedes
   decoding. These regressions deliberately record that existing ABI policy. *)
Lemma int32_to_bool_zero : forall m,
  exists cv,
  Cop.sem_cast (Values.Vint (Int.repr 0)) (Ctypes.Tint I32 Signed noattr)
    (transBeePL_type (Vtype Tbool)) m = Some cv /\
  decode_memory_value (Vtype Tbool) cv = OK (Vbool false).
Proof. intros; eexists; split; reflexivity. Qed.

Lemma int32_to_bool_one : forall m,
  exists cv,
  Cop.sem_cast (Values.Vint (Int.repr 1)) (Ctypes.Tint I32 Signed noattr)
    (transBeePL_type (Vtype Tbool)) m = Some cv /\
  decode_memory_value (Vtype Tbool) cv = OK (Vbool true).
Proof. intros; eexists; split; reflexivity. Qed.

Lemma int32_to_bool_truncates_256 : forall m,
  exists cv,
  Cop.sem_cast (Values.Vint (Int.repr 256)) (Ctypes.Tint I32 Signed noattr)
    (transBeePL_type (Vtype Tbool)) m = Some cv /\
  decode_memory_value (Vtype Tbool) cv = OK (Vbool false).
Proof. intros; eexists; split; reflexivity. Qed.
