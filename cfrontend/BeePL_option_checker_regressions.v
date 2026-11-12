(* Executable checker regressions for nullable references and lexical option
   branches. These check source typing behavior, not runtime memory validity. *)
Require Import List ZArith Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typechecker.
Import ListNotations.

Definition option_test_inner := Reftype (Bprim (Tint I32 Signed noattr)) noattr.
Definition option_test_ref := Ptrtype option_test_inner.
Definition option_test_type := Ptrtype (Otype option_test_inner).
Definition option_test_integer := Vtype (Tint I32 Signed noattr).
Definition option_test_some := Esome (Val (Vloc 2%positive Ptrofs.zero) option_test_ref) option_test_type.
Definition option_test_read := Prim Deref [Var 1%positive option_test_ref] option_test_integer.
Definition option_test_zero := Const (ConsInt Int.zero) option_test_integer.
(* The accepted reference literal must have its declared root in the store
   context; lexical option tests should not rely on accepting forged values. *)
Definition option_test_store := PTree.set 2%positive option_test_ref empty_stcontext.
Definition option_test_check e := type_check_expr (PTree.empty _) empty_context option_test_store e.

Example checker_some_reference_payload :
  option_test_check option_test_some = OK (option_test_type, []).
Proof. vm_compute. reflexivity. Qed.

Example checker_some_then_none_pointer_binding :
  option_test_check
    (Match option_test_some [Psome 1%positive; Pnone]
      [option_test_read; option_test_zero] option_test_integer) =
  OK (option_test_integer, [Read]).
Proof. vm_compute. reflexivity. Qed.

Example checker_none_then_some_pointer_binding :
  option_test_check
    (Match (Enone option_test_type) [Pnone; Psome 1%positive]
      [option_test_zero; option_test_read] option_test_integer) =
  OK (option_test_integer, [Read]).
Proof. vm_compute. reflexivity. Qed.

Example checker_some_binder_does_not_leak_into_later_none :
  exists error, option_test_check
    (Match option_test_some [Psome 1%positive; Pnone]
      [option_test_read; option_test_read] option_test_integer) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Example checker_some_binder_does_not_leak_into_earlier_none :
  exists error, option_test_check
    (Match (Enone option_test_type) [Pnone; Psome 1%positive]
      [option_test_read; option_test_read] option_test_integer) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Example checker_some_payload_is_not_the_pointed_to_integer :
  exists error, option_test_check (Esome option_test_zero option_test_type) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Example checker_nested_none_rejected :
  exists error, option_test_check
    (Enone (Ptrtype (Otype (Otype option_test_inner)))) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Example checker_nested_some_rejected :
  exists error, option_test_check
    (Esome option_test_some (Ptrtype (Otype (Otype option_test_inner)))) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Example checker_some_binder_not_a_scalar :
  exists error, option_test_check
    (Match option_test_some [Pnone; Psome 1%positive]
      [option_test_zero; Var 1%positive option_test_integer] option_test_integer) = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.

Print Assumptions checker_some_then_none_pointer_binding.
Print Assumptions checker_some_binder_does_not_leak_into_later_none.
Print Assumptions checker_nested_some_rejected.

Example checker_some_unregistered_reference_rejected :
  exists error,
    type_check_expr (PTree.empty _) empty_context empty_stcontext
      option_test_some = Errors.Error error.
Proof. vm_compute. eexists; reflexivity. Qed.
