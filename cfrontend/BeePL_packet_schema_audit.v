(* Regressions closing the volatile-header schema gap. Both declarative
   schemas and the executable checker now reject the unsafe producer. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker.
Require Import BeePL_structure_source_regressions BeePL_soundness_store BeePL_storage_types.
Import ListNotations.

Example volatile_header_schema_rejected :
  ~ packet_schema_valid volatile_field_environment 1%positive [(2%positive,volatile_field_type)].
Proof.
  intros [co [Hg [Hs [Hm [Hf Hstorage]]]]].
  vm_compute in Hstorage. discriminate.
Qed.

Example volatile_header_storage_rejected :
  storage_type_check volatile_field_environment (Stype 1%positive noattr) = false.
Proof. vm_compute; reflexivity. Qed.

Definition volatile_packet_match : expr :=
  Match (Var 3%positive Bytes)
    [Pbytes 4%positive (Stype 1%positive noattr) [(2%positive,volatile_field_type)];
     Pbytes 5%positive Bytes []]
    [Val Vunit Utype; Val Vunit Utype] Utype.

Example volatile_header_match_checker_rejected :
  exists error, type_check_expr volatile_field_environment
    (extend_context empty_context 3%positive Bytes) empty_stcontext volatile_packet_match =
    Error error.
Proof. vm_compute; eexists; reflexivity. Qed.

Theorem volatile_header_cell_impossible : forall env Sigma m b ofs chunk,
  ~ typed_memory_cell env Sigma m b ofs volatile_field_type chunk.
Proof.
  intros * Hcell.
  pose proof (typed_cell_nonvolatile _ _ _ _ _ _ _ Hcell) as Hnonvolatile.
  discriminate Hnonvolatile.
Qed.

Require Import BeePL_packet_schema_check.
Example safe_schema_validator_rejects_volatile_header :
  packet_schema_check volatile_field_environment 1%positive [(2%positive,volatile_field_type)] = false.
Proof. vm_compute; reflexivity. Qed.
Example safe_schema_validator_accepts_boolean_header :
  packet_schema_check boolean_field_environment 1%positive [(2%positive,Vtype Tbool)] = true.
Proof. vm_compute; reflexivity. Qed.
Example safe_schema_validator_rejects_mismatched_field :
  packet_schema_check boolean_field_environment 1%positive
    [(2%positive,Vtype(Tint I8 Unsigned noattr))] = false.
Proof. vm_compute; reflexivity. Qed.
Example safe_schema_validator_rejects_unknown_schema :
  packet_schema_check boolean_field_environment 17%positive [] = false.
Proof. vm_compute; reflexivity. Qed.

Definition boolean_packet_match (attr : attr) (fields : list (ident * type)) : expr :=
  Match (Var 3%positive Bytes)
    [Pbytes 4%positive (Stype 1%positive attr) fields; Pbytes 5%positive Bytes []]
    [Val (Vbool true) (Vtype Tbool); Val (Vbool false) (Vtype Tbool)] (Vtype Tbool).
Example safe_boolean_packet_match_accepted :
  type_check_expr boolean_field_environment
    (extend_context empty_context 3%positive Bytes) empty_stcontext
    (boolean_packet_match noattr [(2%positive,Vtype Tbool)]) = OK(Vtype Tbool,[]).
Proof. vm_compute; reflexivity. Qed.
Example packet_field_annotation_mismatch_rejected :
  exists error, type_check_expr boolean_field_environment
    (extend_context empty_context 3%positive Bytes) empty_stcontext
    (boolean_packet_match noattr [(2%positive,Vtype(Tint I8 Unsigned noattr))]) = Error error.
Proof. vm_compute; eexists; reflexivity. Qed.
Example noncanonical_packet_pattern_rejected :
  exists error, type_check_expr boolean_field_environment
    (extend_context empty_context 3%positive Bytes) empty_stcontext
    (boolean_packet_match {|attr_volatile:=false;attr_alignas:=Some 3%N|}
      [(2%positive,Vtype Tbool)]) = Error error.
Proof. vm_compute; eexists; reflexivity. Qed.
