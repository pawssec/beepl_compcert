(* Array initialization cannot store direct function values. The strengthened
   storage check rejects the former progress counterexample. Its operational
   failure remains documented independently of code-address authenticity. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Globalenvs Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_runtime_locations BeePL_callable_locations.
Require Import BeePL_aggregate_memory BeePL_function_parameters.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_layout_coherence.
Require Import BeePL_storage_types BeePL_typechecker.
Import ListNotations.

Definition function_array_element_type : type := Ftype [] [] Utype false.
Definition function_array_type : type := Atype function_array_element_type 1 noattr.
Definition function_array_initializer (arr : ident) (code : Values.block) : expr :=
  Ainit arr function_array_type
    [Val (Vloc code Ptrofs.zero) function_array_element_type] function_array_type.

Theorem function_array_initializer_rejected : forall cenv Gamma Sigma arr code ef ty,
  ~ type_expr cenv Gamma Sigma (function_array_initializer arr code) ef ty.
Proof.
  intros cenv Gamma Sigma arr code ef ty Htyped.
  unfold function_array_initializer in Htyped. inversion Htyped; subst.
  match goal with Hstorage : storage_type_check _ _ = true |- _ =>
    unfold function_array_type, function_array_element_type in Hstorage;
    rewrite storage_type_function_array_rejected in Hstorage; discriminate
  end.
Qed.

Theorem function_array_checker_rejected : forall cenv Gamma Sigma arr code,
  exists error, type_check_expr cenv Gamma Sigma (function_array_initializer arr code) = Error error.
Proof.
  intros. unfold function_array_initializer, function_array_type, function_array_element_type.
  cbn [type_check_expr type_check_exprs BeePL_value_checker.value_type_check].
  rewrite storage_type_function_array_rejected. eexists; reflexivity.
Qed.

Theorem function_array_initializer_located : forall (ge : genv) cells objects arr code fn,
  Genv.find_funct ge (Values.Vptr code Ptrofs.zero) = Some (Internal fn) ->
  type_of_function fn = function_array_element_type ->
  runtime_locations (descriptor_heap_locations ge cells objects)
    (function_array_initializer arr code).
Proof.
  intros ge cells objects arr code fn Hfind Hsignature.
  split; [|exact I]. left.
  change (internal_code_locations ge code Ptrofs.zero function_array_element_type).
  split; [reflexivity|]. exists [], [], Utype, false, fn.
  repeat split; assumption || reflexivity.
Qed.

Lemma function_array_helper_impossible : forall ge m block offset code final,
  ~ sem_array_init_helper ge m block offset [Vloc code Ptrofs.zero]
      function_array_element_type final.
Proof.
  intros ge m block offset code final Hinit. inversion Hinit; subst.
  eapply function_full_assignment_impossible; eauto.
Qed.

Theorem function_array_initializer_stuck : forall ge p vm m arr code final vm' result,
  ~ ssem_expr ge p vm m (function_array_initializer arr code) final vm' result.
Proof.
  intros ge p vm m arr code final vm' result Hstep.
  unfold function_array_initializer in Hstep. inversion Hstep; subst.
  - eapply value_has_no_small_step; eauto.
  - discriminate.
  - match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion Hinit; subst
    end.
    match goal with Hshape : function_array_type = Atype _ _ _ |- _ =>
      unfold function_array_type in Hshape; inversion Hshape; subst
    end.
    eapply function_array_helper_impossible. exact H3.
Qed.

Theorem function_array_initializer_not_value : forall arr code,
  is_value (function_array_initializer arr code) = false.
Proof. reflexivity. Qed.

Definition function_array_no_objects : aggregate_object_context := fun _ _ _ => False.
Definition function_array_no_cells : scalar_layout := fun _ _ _ _ => False.

(* The old coherent-configuration witness is now excluded by source typing,
   even though the independently checked code location can be authentic. *)
Theorem function_array_initializer_not_coherent : forall (ge : genv) m packets arr code ef ty,
  ~ coherent_runtime_configuration ge empty_context empty_stcontext empty_vmap m
    function_array_no_objects function_array_no_cells packets
    (function_array_initializer arr code) ef ty.
Proof.
  intros ge m packets arr code ef ty [[Hheap Htyped Hlocations Hframes] Hcoherent].
  eapply function_array_initializer_rejected; exact Htyped.
Qed.

Print Assumptions function_array_initializer_rejected.
Print Assumptions function_array_checker_rejected.
Print Assumptions function_array_initializer_located.
Print Assumptions function_array_initializer_stuck.
Print Assumptions function_array_initializer_not_coherent.
