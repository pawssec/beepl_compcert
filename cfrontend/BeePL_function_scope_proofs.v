(* Function-local storage declarations do not introduce initialized source
   variables. Only globals, parameters, and lexical binders enter typing. *)
Require Import List String Coqlib Maps AST Errors Integers Ctypes.
Require Import BeePL_parameter_storage_check BeePL_storage_types.
Require Import BeeTypes BeePL_values BeePL_aux BeePL BeePL_typesystem BeePL_typechecker.
Import ListNotations.
Local Open Scope list_scope.

Lemma unbound_variable_not_typed : forall cenv Gamma Sigma x t ef result,
  PTree.get x Gamma = None ->
  ~ type_expr cenv Gamma Sigma (Var x t) ef result.
Proof.
  intros cenv Gamma Sigma x t ef result Hmissing Htyped.
  inversion Htyped; subst. congruence.
Qed.

(* [fn_vars] is deliberately unrestricted: even listing [x] there cannot
   justify reading it before its lexical initializer. *)
Theorem function_local_slot_not_in_scope : forall cenv Gamma Sigma fn x t,
  fn.(fn_args) = nil ->
  fn.(fn_body) = Var x t ->
  PTree.get x Gamma = None ->
  ~ type_function cenv Gamma Sigma fn.
Proof.
  intros cenv Gamma Sigma fn x t Hargs Hbody Hmissing Htyped.
  inversion Htyped; subst.
  rewrite Hargs in *. simpl in *.
  match goal with
  | Hbodytyped : type_expr _ _ _ (fn_body fn) _ _ |- _ =>
      rewrite Hbody in Hbodytyped;
      eapply unbound_variable_not_typed; eauto
  end.
Qed.

Lemma initialized_lexical_binding_typed : forall cenv Gamma Sigma x,
  type_expr cenv Gamma Sigma
    (Bind x Utype (Const ConsUnit Utype) (Var x Utype) Utype) nil Utype.
Proof.
  intros. change (@nil effect_label) with ((@nil effect_label) ++ nil).
  eapply ty_bind.
  - apply ty_constunit.
  - apply ty_var. unfold extend_context. apply PTree.gss.
Qed.

Theorem initialized_lexical_function_typed : forall cenv Gamma Sigma fn x,
  fn.(fn_args) = nil ->
  fn.(fn_body) = Bind x Utype (Const ConsUnit Utype) (Var x Utype) Utype ->
  fn.(fn_return) = Utype -> fn.(fn_effect) = nil ->
  type_function cenv Gamma Sigma fn.
Proof.
  intros cenv Gamma Sigma fn x Hargs Hbody Hreturn Heffect.
  eapply ty_function with (Gamma' := Gamma) (ef := nil) (tb := Utype).
  all: try (rewrite Hargs; simpl; constructor).
  all: try (rewrite Hbody; apply initialized_lexical_binding_typed).
  all: try (rewrite Hreturn; reflexivity).
  all: try (rewrite Heffect; reflexivity).
  all: reflexivity.
Qed.

Theorem function_parameter_read_typed : forall cenv Gamma Sigma fn x t,
  fn.(fn_args) = [(x, t)] -> fn.(fn_body) = Var x t ->
  fn.(fn_return) = t -> fn.(fn_effect) = nil ->
  is_ptrtype t = false -> parameter_storage_check cenv t = true ->
  type_function cenv Gamma Sigma fn.
Proof.
  intros cenv Gamma Sigma fn x t Hargs Hbody Hreturn Heffect Hnonptr Hstorage.
  eapply ty_function with (Gamma' := bind_vars Gamma [(x, t)])
    (ef := nil) (tb := t).
  all: try (rewrite Hargs; reflexivity).
  all: try (rewrite Hargs; simpl; repeat constructor; simpl; tauto).
  all: try (rewrite Hbody; apply ty_var; simpl; unfold extend_context; apply PTree.gss).
  all: try (rewrite Hreturn; reflexivity).
  all: try (rewrite Heffect; reflexivity).
  all: try (rewrite Hargs; unfold parameters_storage_check; simpl; rewrite Hstorage; reflexivity).
  all: assumption.
Qed.

Lemma unbound_variable_checker_rejected : forall cenv Gamma Sigma x t,
  PTree.get x Gamma = None ->
  exists error, type_check_expr cenv Gamma Sigma (Var x t) = Errors.Error error.
Proof.
  intros. simpl. rewrite H. eexists; reflexivity.
Qed.

Lemma initialized_lexical_binding_checker : forall cenv Gamma Sigma x,
  type_check_expr cenv Gamma Sigma
    (Bind x Utype (Const ConsUnit Utype) (Var x Utype) Utype) =
    OK (Utype, nil).
Proof.
  intros. simpl. unfold extend_context. rewrite PTree.gss. reflexivity.
Qed.

Theorem function_local_slot_checker_rejected : forall cenv Gamma Sigma fn x t,
  fn.(fn_args) = nil -> fn.(fn_body) = Var x t ->
  PTree.get x Gamma = None ->
  exists error, type_check_function cenv Gamma Sigma fn = Errors.Error error.
Proof.
  intros cenv Gamma Sigma fn x t Hargs Hbody Hmissing.
  unfold type_check_function. rewrite Hargs, Hbody. simpl.
  rewrite Hmissing. eexists; reflexivity.
Qed.

Theorem initialized_lexical_function_checker : forall cenv Gamma Sigma fn x,
  fn.(fn_args) = nil ->
  fn.(fn_body) = Bind x Utype (Const ConsUnit Utype) (Var x Utype) Utype ->
  fn.(fn_return) = Utype -> fn.(fn_effect) = nil ->
  exists success, type_check_function cenv Gamma Sigma fn = OK success.
Proof.
  intros cenv Gamma Sigma fn x Hargs Hbody Hreturn Heffect.
  unfold type_check_function. rewrite Hargs, Hbody, Hreturn, Heffect.
  simpl. unfold extend_context. rewrite PTree.gss. eexists; reflexivity.
Qed.

(* Duplicate names must be rejected even when their declared types differ. *)
Theorem duplicate_parameter_names_checker_rejected : forall cenv Gamma Sigma fn x t1 t2,
  fn.(fn_args) = [(x, t1); (x, t2)] ->
  exists error, type_check_function cenv Gamma Sigma fn = Errors.Error error.
Proof.
  intros cenv Gamma Sigma fn x t1 t2 Hargs.
  unfold type_check_function. rewrite Hargs.
  destruct (parameters_storage_check cenv [(x,t1);(x,t2)]) eqn:Hstorage; [|eexists;reflexivity].
  match goal with
  | |- context [list_norepet_dec ?dec ?names] =>
      destruct (list_norepet_dec dec names) as [Hunique|Hduplicate]
  end.
  - simpl in Hunique. inversion Hunique; subst. simpl in *. tauto.
  - eexists; reflexivity.
Qed.

Theorem function_unit_parameter_checker : forall cenv Gamma Sigma fn x,
  fn.(fn_args) = [(x, Utype)] -> fn.(fn_body) = Var x Utype ->
  fn.(fn_return) = Utype -> fn.(fn_effect) = nil ->
  exists success, type_check_function cenv Gamma Sigma fn = OK success.
Proof.
  intros cenv Gamma Sigma fn x Hargs Hbody Hreturn Heffect.
  unfold type_check_function. rewrite Hargs, Hbody, Hreturn, Heffect.
  assert(Hstorage:parameters_storage_check cenv [(x,Utype)]=true).
  { unfold parameters_storage_check,parameter_storage_check; simpl. rewrite storage_unit_admissible;reflexivity. }
  rewrite Hstorage. simpl. rewrite PTree.gss. eexists; reflexivity.
Qed.

Lemma lexical_initializer_type_mismatch_rejected :
  forall cenv Gamma Sigma x declared e1 e2 result inferred ef,
  type_check_expr cenv Gamma Sigma e1 = OK (inferred, ef) ->
  eq_type inferred declared = false ->
  exists error, type_check_expr cenv Gamma Sigma
    (Bind x declared e1 e2 result) = Errors.Error error.
Proof.
  intros cenv Gamma Sigma x declared e1 e2 result inferred ef Hcheck Hmismatch.
  simpl. rewrite Hcheck. simpl.
  destruct (type_check_expr cenv (extend_context Gamma x declared) Sigma e2)
    as [[bodytype bodyeffect]|error]; simpl.
  - rewrite Hmismatch. simpl. eexists; reflexivity.
  - eexists; reflexivity.
Qed.
