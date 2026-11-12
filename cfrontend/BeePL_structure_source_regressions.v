(* Struct initialization preserves BeePL Bool instead of round-tripping it
   through unsigned-byte C types. Both existing result representations work. *)
Require Import List ZArith Lia AST Integers Maps Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_typechecker.
Import ListNotations.
Local Open Scope Z_scope.
Definition boolean_field_composite : bcomposite.
Proof.
  refine {| co_su := Struct; co_members := [BeeTypes.Member_plain 2%positive (Vtype Tbool)];
    co_attr := noattr; co_sizeof := 1; co_alignof := 1; co_rank := 0%nat |}.
  - lia.
  - exists 0%nat. reflexivity.
  - exists 1; lia.
Defined.
Definition boolean_field_environment : bcomposite_env :=
  PTree.set 1%positive boolean_field_composite (PTree.empty bcomposite).
Definition boolean_struct_value : type := Stype 1%positive noattr.
Definition boolean_struct_reference : type := Ptrtype (Reftype (Bstruct 1%positive noattr) noattr).
Definition initialize_boolean_struct (result : type) (value : expr) : expr :=
  Sinit 1%positive [2%positive] [value] result.

Example direct_boolean_struct_checks :
  type_check_expr boolean_field_environment empty_context empty_stcontext
    (initialize_boolean_struct boolean_struct_value (Val (Vbool true) (Vtype Tbool))) =
  OK (boolean_struct_value, []).
Proof. vm_compute; reflexivity. Qed.
Example reference_boolean_struct_checks :
  type_check_expr boolean_field_environment empty_context empty_stcontext
    (initialize_boolean_struct boolean_struct_reference (Val (Vbool true) (Vtype Tbool))) =
  OK (boolean_struct_reference, []).
Proof. vm_compute; reflexivity. Qed.
Example direct_uint8_as_bool_rejected :
  exists error, type_check_expr boolean_field_environment empty_context empty_stcontext
    (initialize_boolean_struct boolean_struct_value
      (Val (Vint (Int.repr 1)) (Vtype (Tint I8 Unsigned noattr)))) = Errors.Error error.
Proof. eexists; vm_compute; reflexivity. Qed.
Example reference_uint8_as_bool_rejected :
  exists error, type_check_expr boolean_field_environment empty_context empty_stcontext
    (initialize_boolean_struct boolean_struct_reference
      (Val (Vint (Int.repr 1)) (Vtype (Tint I8 Unsigned noattr)))) = Errors.Error error.
Proof. eexists; vm_compute; reflexivity. Qed.

Theorem both_boolean_struct_forms_typed : forall result,
  structure_result_type 1%positive noattr result ->
  type_expr boolean_field_environment empty_context empty_stcontext
    (initialize_boolean_struct result (Val (Vbool true) (Vtype Tbool))) [] result.
Proof.
  intros result Hresult. unfold initialize_boolean_struct.
  eapply ty_sinit with (id := 1%positive) (a := noattr)
    (co := boolean_field_composite) (bts := [Vtype Tbool]).
  - reflexivity.
  - exact Hresult.
  - eapply ty_cons with (ef := []) (efs := []); constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
Qed.
Print Assumptions both_boolean_struct_forms_typed.

Definition volatile_field_type : type :=
  Vtype (Tint I32 Signed {| attr_volatile := true; attr_alignas := None |}).
Definition volatile_field_composite : bcomposite.
Proof.
  refine {| co_su := Struct; co_members := [BeeTypes.Member_plain 2%positive volatile_field_type];
    co_attr := noattr; co_sizeof := 4; co_alignof := 4; co_rank := 0%nat |}.
  - lia.
  - exists 2%nat. reflexivity.
  - exists 1; lia.
Defined.
Definition volatile_field_environment : bcomposite_env :=
  PTree.set 1%positive volatile_field_composite (PTree.empty bcomposite).
Definition initialize_volatile_struct (result : type) : expr :=
  Sinit 1%positive [2%positive]
    [Const (ConsInt Int.zero) volatile_field_type] result.

Example direct_volatile_struct_rejected :
  exists error, type_check_expr volatile_field_environment empty_context empty_stcontext
    (initialize_volatile_struct (Stype 1%positive noattr)) = Error error.
Proof. vm_compute; eexists; reflexivity. Qed.

(* A nonvolatile result pointer must not hide a volatile constructed field. *)
Example reference_volatile_struct_rejected :
  exists error, type_check_expr volatile_field_environment empty_context empty_stcontext
    (initialize_volatile_struct (Ptrtype (Reftype (Bstruct 1%positive noattr) noattr))) = Error error.
Proof. vm_compute; eexists; reflexivity. Qed.
