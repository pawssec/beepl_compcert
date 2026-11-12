(* A program's typed-code contract does not restrict every function to the
   signature of one particular call. Supported parameter storage is checked
   separately at the selected call site. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_callable_entry.

Definition internal_code_contract (bge : genv) (globals : ty_context)
    (Sigma : store_context) : Prop :=
  forall b fn,
    Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    type_function bge.(genv_cenv) globals Sigma fn.

Lemma internal_code_contract_store_extension : forall bge globals Sigma Sigma',
  internal_code_contract bge globals Sigma -> store_context_extends Sigma Sigma' ->
  internal_code_contract bge globals Sigma'.
Proof.
  intros bge globals Sigma Sigma' Hcode Hext b fn Hfind.
  eapply function_typing_store_extension; [apply (Hcode b fn Hfind) | exact Hext].
Qed.

Lemma primitive_code_contract_typed : forall bge globals Sigma,
  primitive_internal_code_contract bge globals Sigma ->
  internal_code_contract bge globals Sigma.
Proof. intros bge globals Sigma Hcode b fn Hfind. exact (proj1 (Hcode b fn Hfind)). Qed.

Print Assumptions internal_code_contract_store_extension.
Print Assumptions primitive_code_contract_typed.
