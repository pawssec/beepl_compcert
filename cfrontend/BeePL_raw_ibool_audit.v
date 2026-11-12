(* Raw Coq IBool is admitted by current formal source checks but is not a
   surface BeePL primitive. This audit makes that compiler-scope gap explicit. *)
Require Import List String ZArith Integers AST Maps Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker.
Require Import BeePL_escape_types BeePL_escape_check.
Import ListNotations.

Definition raw_ibool := Vtype (Tint IBool Unsigned noattr).
Definition raw_ibool_function : function :=
  {| fn_return := raw_ibool; fn_effect := []; fn_callconv := cc_default;
     fn_args := []; fn_vars := [];
     fn_body := Const (ConsInt (Int.repr 2)) raw_ibool; is_ebpf := false |}.
Lemma raw_ibool_composites_wf : wf_bcomposites [].
Proof. vm_compute. exact I. Qed.
Definition raw_ibool_program : program := @mkbprogram []
  [(1%positive,Gfun(Internal raw_ibool_function),None)] [1%positive] 1%positive
  raw_ibool_composites_wf [].

Example raw_ibool_function_declarative : forall cenv Gamma Sigma,
  type_function cenv Gamma Sigma raw_ibool_function.
Proof.
  intros. eapply ty_function with (ef:=[]) (tb:=raw_ibool) (Gamma':=Gamma);
    try reflexivity.
  - constructor.
  - apply ty_constint.
Qed.
Example raw_ibool_program_declarative : type_program raw_ibool_program.
Proof.
  eapply ty_prog; [reflexivity|reflexivity|reflexivity|].
  constructor; [|constructor]. eapply ty_fundef; [reflexivity|].
  eapply ty_ifundef; [reflexivity|apply raw_ibool_function_declarative].
Qed.
Example raw_ibool_program_checker_accepts :
  exists message, type_check_program raw_ibool_program=OK message.
Proof. vm_compute. eexists; reflexivity. Qed.
Example raw_ibool_escape_gate_accepts : escape_program_check raw_ibool_program=true.
Proof. vm_compute; reflexivity. Qed.
Example raw_ibool_value_two_declarative : forall cenv Gamma Sigma,
  type_expr cenv Gamma Sigma (Val(Vint(Int.repr 2))raw_ibool) [] raw_ibool.
Proof. intros; constructor. Qed.
Example raw_ibool_source_access : access_mode_type raw_ibool=By_value Mint8unsigned.
Proof. reflexivity. Qed.
Example raw_ibool_target_access : access_mode(transBeePL_type raw_ibool)=By_value Mbool.
Proof. reflexivity. Qed.
Print Assumptions raw_ibool_program_declarative.
Print Assumptions raw_ibool_program_checker_accepts.
Print Assumptions raw_ibool_escape_gate_accepts.
