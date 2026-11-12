(* Code aliases use no mutable data slot. This semantic regression does not
   claim support for indirect calls in the eBPF compiler backend. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Import ListNotations.

Theorem singleton_code_parameter_no_storage : forall (ge : genv) Sigma m id b fn,
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  let signature := type_of_function fn in
  let callee := PTree.set id (b, signature) empty_vmap in
  function_parameter_partition ge [(id, signature)] [Vloc b Ptrofs.zero] callee [] [] /\
  alloc_variables ge Sigma callee m [] callee m Sigma /\
  bind_variables ge callee m [] [] m.
Proof.
  intros ge Sigma m id b fn Hfind. unfold type_of_function. simpl.
  split; [eapply function_partition_code; [exact Hfind|reflexivity|constructor]|].
  split; constructor.
Qed.

Theorem singleton_code_parameter_local_read : forall (ge : genv) p Sigma m id b fn,
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  let signature := type_of_function fn in
  let callee := PTree.set id (b, signature) empty_vmap in
  ssem_expr ge p callee m (Var id signature) m callee (Val (Vloc b Ptrofs.zero) signature) /\
  type_expr ge.(genv_cenv) (PTree.set id signature empty_context) Sigma
    (Val (Vloc b Ptrofs.zero) signature) nil signature.
Proof.
  intros ge p Sigma m id b fn Hfind. unfold type_of_function. simpl.
  split.
  - eapply ssem_local_function; [apply PTree.gss|exact Hfind|reflexivity].
  - apply ty_valfun.
Qed.

Print Assumptions singleton_code_parameter_no_storage.
Print Assumptions singleton_code_parameter_local_read.
