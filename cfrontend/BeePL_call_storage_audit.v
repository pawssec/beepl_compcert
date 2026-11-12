(* General parameter preparation exposes a source typing gap: attributed
   scalar values are legal, but ordinary parameter stores cannot be volatile. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Coqlib.
Require Import BeePL_parameter_storage_check BeePL_storage_types BeePL_typechecker.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_volatile_audit.
Import ListNotations.

Definition volatile_parameter_function : function :=
  {| fn_return:=Utype; fn_effect:=[]; fn_callconv:=cc_default;
     fn_args:=[(1%positive,Vtype audit_volatile_int)]; fn_vars:=[];
     fn_body:=Val Vunit Utype; is_ebpf:=false |}.

Lemma volatile_parameter_storage_rejected : forall env,
  parameters_storage_check env volatile_parameter_function.(fn_args)=false.
Proof.
  intros env. destruct(parameters_storage_check env volatile_parameter_function.(fn_args)) eqn:Hcheck;[|reflexivity].
  assert(Hstore:storage_type_check env (Vtype audit_volatile_int)=true).
  { eapply parameters_storage_data_member;[exact Hcheck|simpl;auto|reflexivity]. }
  apply storage_type_nonvolatile in Hstore. discriminate.
Qed.

Theorem volatile_parameter_function_rejected : forall env Gamma Sigma,
  ~ type_function env Gamma Sigma volatile_parameter_function.
Proof.
  intros env Gamma Sigma Htype. inversion Htype;subst.
  match goal with Hcheck:parameters_storage_check _ _=true |- _ =>
    rewrite volatile_parameter_storage_rejected in Hcheck;discriminate end.
Qed.

Theorem volatile_parameter_function_checker_rejected : forall env Gamma Sigma,
  exists error, type_check_function env Gamma Sigma volatile_parameter_function=Errors.Error error.
Proof.
  intros. unfold type_check_function. rewrite volatile_parameter_storage_rejected. eexists;reflexivity.
Qed.

Theorem volatile_parameter_value_typed : forall env Gamma Sigma,
  type_expr env Gamma Sigma (Val(Vint Int.zero)(Vtype audit_volatile_int)) [] (Vtype audit_volatile_int).
Proof. intros; constructor. Qed.

Theorem volatile_parameter_assignment_impossible : forall ge m b final result,
  ~ assign_addr ge (Vtype audit_volatile_int) m b Ptrofs.zero Full (Vint Int.zero) final result.
Proof.
  intros * Hass. inversion Hass; subst; try discriminate.
Qed.

Theorem volatile_parameter_binding_impossible : forall ge vm m final,
  ~ bind_variables ge vm m [(1%positive,Vtype audit_volatile_int)] [Vint Int.zero] final.
Proof.
  intros * Hbind. inversion Hbind; subst.
  eapply volatile_parameter_assignment_impossible; eauto.
Qed.

Print Assumptions volatile_parameter_function_rejected.
Print Assumptions volatile_parameter_binding_impossible.
