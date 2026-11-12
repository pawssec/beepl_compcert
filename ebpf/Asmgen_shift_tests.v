(* Checked 64-bit unsigned register-shift lowering and ALU semantics. *)
Require Import Coqlib Errors AST Integers Values Op Locations Mach Asm Asmgen.
Require Import Asmgenproof1 List.
Import ListNotations.

Example unsigned_long_register_shift_emission :
  transl_op 0 Oshrlu [I1;I2] I1 [] = OK [Palu RSH W64 R1 (inl R2)].
Proof. vm_compute; reflexivity. Qed.
Example unsigned_long_alias_shift_emission :
  transl_op 0 Oshrlu [I1;I1] I1 [] = OK [Palu RSH W64 R1 (inl R1)].
Proof. vm_compute; reflexivity. Qed.
Example unsigned_long_wrong_destination_rejected :
  exists message, transl_op 0 Oshrlu [I1;I2] I3 [] = Error message.
Proof. vm_compute; eexists; reflexivity. Qed.
Example unsigned_long_wrong_arity_rejected :
  exists message, transl_op 0 Oshrlu [I1] I1 [] = Error message.
Proof. vm_compute; eexists; reflexivity. Qed.

(* The count is a 32-bit integer, as required by Op.type_of_operation;
   eval_alu deliberately uses W32 for the shift count even at W64 width. *)
Lemma unsigned_long_register_shift_semantics : forall value count,
  eval_alu RSH W64 value (inl count) = Some (Val.shrlu value count).
Proof. reflexivity. Qed.
Example unsigned_long_high_bit_zero_fill :
  eval_alu RSH W64 (Vlong (Int64.repr (-1))) (inl (Vint (Int.repr 63))) =
  Some (Vlong Int64.one).
Proof. vm_compute; reflexivity. Qed.
Example unsigned_long_zero_shift :
  eval_alu RSH W64 (Vlong (Int64.repr 42)) (inl (Vint Int.zero)) =
  Some (Vlong (Int64.repr 42)).
Proof. vm_compute; reflexivity. Qed.
Example unsigned_long_out_of_range :
  eval_alu RSH W64 (Vlong (Int64.repr 42)) (inl (Vint (Int.repr 64))) =
  Some Vundef.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions transl_op_correct.
Print Assumptions unsigned_long_register_shift_semantics.
