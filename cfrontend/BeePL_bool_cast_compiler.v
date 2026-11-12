(* Executable Cstrategy regressions for compiler Bool normalization. These
   evaluate the generated nested casts/comparison, not just the raw cast.
   They preserve BeePL's existing uint8 truncation-before-decoding policy. *)
Require Import List ZArith Integers Values AST Memory Ctypes Csyntax Cstrategy Cop Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_mem BeePL_Csyntax.

Lemma generated_bool_cast_type : forall operand,
  Csyntax.typeof (trans_cast_expression (Vtype Tbool) operand) = transBeePL_type (Vtype Tbool).
Proof. reflexivity. Qed.

Lemma generated_nonbool_cast_unchanged : forall target operand,
  target <> Vtype Tbool ->
  trans_cast_expression target operand = Ecast operand (transBeePL_type target).
Proof.
  intros target operand Htarget. destruct target; try reflexivity.
  destruct p; try reflexivity; contradiction.
Qed.

Theorem generated_bool_cast_normalizes : forall ge env m operand cv raw v,
  eval_simple_rvalue ge env m operand cv ->
  Cop.sem_cast cv (Csyntax.typeof operand) (transBeePL_type (Vtype Tbool)) m = Some raw ->
  decode_memory_value (Vtype Tbool) raw = OK v ->
  eval_simple_rvalue ge env m (trans_cast_expression (Vtype Tbool) operand)
    (trans_bvalue_cvalue v).
Proof.
  intros ge env m operand cv raw v Heval Hcast Hdecode.
  destruct raw; simpl in Hdecode; try discriminate.
  inversion Hdecode; subst v.
  unfold trans_cast_expression. simpl.
  eapply esr_cast with (v1 := Val.of_bool (negb (Int.eq i Int.zero))).
  - eapply esr_binop with (v1 := Values.Vint i) (v2 := Values.Vint Int.zero).
    + eapply esr_cast; [exact Heval | exact Hcast].
    + apply esr_val.
    + reflexivity.
  - destruct (Int.eq i Int.zero); reflexivity.
Qed.

Theorem generated_bool_cast_two_is_one : forall ge env m,
  eval_simple_rvalue ge env m
    (trans_cast_expression (Vtype Tbool)
      (Eval (Values.Vint (Int.repr 2)) (Ctypes.Tint I32 Signed noattr)))
    (Values.Vint Int.one).
Proof.
  intros. unfold trans_cast_expression. simpl.
  eapply esr_cast with (v1 := Values.Vint Int.one).
  - eapply esr_binop with (v1 := Values.Vint (Int.repr 2)) (v2 := Values.Vint Int.zero).
    + eapply esr_cast with (v1 := Values.Vint (Int.repr 2)); [constructor | reflexivity].
    + constructor.
    + reflexivity.
  - reflexivity.
Qed.

Theorem generated_bool_cast_256_is_zero : forall ge env m,
  eval_simple_rvalue ge env m
    (trans_cast_expression (Vtype Tbool)
      (Eval (Values.Vint (Int.repr 256)) (Ctypes.Tint I32 Signed noattr)))
    (Values.Vint Int.zero).
Proof.
  intros. unfold trans_cast_expression. simpl.
  eapply esr_cast with (v1 := Values.Vint Int.zero).
  - eapply esr_binop with (v1 := Values.Vint Int.zero) (v2 := Values.Vint Int.zero).
    + eapply esr_cast with (v1 := Values.Vint (Int.repr 256)); [constructor | reflexivity].
    + constructor.
    + reflexivity.
  - reflexivity.
Qed.

Example source_bool_cast_two_encoding : forall m,
  exists raw,
    Cop.sem_cast (Values.Vint (Int.repr 2)) (Ctypes.Tint I32 Signed noattr)
      (transBeePL_type (Vtype Tbool)) m = Some raw /\
    decode_memory_value (Vtype Tbool) raw = OK (Vbool true) /\
    trans_bvalue_cvalue (Vbool true) = Values.Vint Int.one.
Proof. intros; eexists; repeat split; reflexivity. Qed.

Example source_bool_cast_256_encoding : forall m,
  exists raw,
    Cop.sem_cast (Values.Vint (Int.repr 256)) (Ctypes.Tint I32 Signed noattr)
      (transBeePL_type (Vtype Tbool)) m = Some raw /\
    decode_memory_value (Vtype Tbool) raw = OK (Vbool false) /\
    trans_bvalue_cvalue (Vbool false) = Values.Vint Int.zero.
Proof. intros; eexists; repeat split; reflexivity. Qed.
Print Assumptions generated_bool_cast_two_is_one.
Print Assumptions generated_bool_cast_256_is_zero.
Print Assumptions source_bool_cast_two_encoding.
Print Assumptions source_bool_cast_256_encoding.

Print Assumptions generated_bool_cast_normalizes.
