(* Direct evaluated calls enter with the same effect bound as their typed
   application. Primitive parameter support remains explicit in the code contract. *)
Require Import List Bool Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_type_equality.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_callable_entry BeePL_call_state.
Require Import BeePL_runtime_frames BeePL_runtime_call_entry BeePL_frame_free.
Import ListNotations.

Lemma evaluated_arguments_effect_nil : forall cenv Gamma Sigma es ef ts,
  type_exprs cenv Gamma Sigma es ef ts ->
  Forall (fun e => exists v annotation, e = Val v annotation) es -> ef = nil.
Proof.
  intros cenv Gamma Sigma es ef ts Htyped. induction Htyped; intros Hvalues; auto.
  inversion Hvalues as [|head tail Hhead Htail]; subst.
  destruct Hhead as [v [annotation Heq]]. subst.
  pose proof (typed_value_effect_nil _ _ _ _ _ _ _ H) as Hef. subst ef.
  simpl. apply IHHtyped. exact Htail.
Qed.

Lemma direct_application_components :
  forall cenv Gamma Sigma v args effects result variadic es ef,
  type_expr cenv Gamma Sigma
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  ef = effects /\
  type_expr cenv Gamma Sigma (Val v (Ftype args effects result variadic)) nil
    (Ftype args effects result variadic) /\
  type_exprs cenv Gamma Sigma es nil args.
Proof.
  intros cenv Gamma Sigma v args effects result variadic es ef Htyped Hvalues.
  inversion Htyped; subst.
  match goal with Hvalue : type_expr _ _ _ (Val v _) _ _ |- _ =>
    pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
    simpl in Hannotation; subst;
    pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hnil; subst
  end.
  match goal with Hcompat : context [eq_type (Ftype args effects result variadic)
      (Ftype ?ts ?efs result ?va)] |- _ =>
    change (eq_type (Ftype args effects result variadic) (Ftype ts efs result va) = true) in Hcompat;
    apply eq_type_sound in Hcompat; inversion Hcompat; subst
  end.
  match goal with Hargs : type_exprs _ _ _ es _ ?types |- _ =>
    pose proof (evaluated_arguments_effect_nil _ _ _ _ _ _ Hargs Hvalues) as Hnil; subst
  end.
  simpl. rewrite app_nil_r. repeat split; assumption || reflexivity.
Qed.

Theorem direct_application_configuration_entry :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef,
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  primitive_internal_code_contract bge globals Sigma ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  (forall b fn, Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (callable_heap_locations bge layout) fn.(fn_body)) ->
  (forall fn, Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) ->
    frame_free fn.(fn_body)) ->
  exists fn callee initialized Sigma',
    ssem_expr bge p caller m
      (App (Val v (Ftype args effects result variadic)) es result)
      initialized caller (CallFrame callee fn.(fn_body) result) /\
    callable_heap_evolution bge Sigma layout Sigma' initialized
      (extended_call_layout layout callee fn.(fn_args)) /\
    primitive_internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller initialized
      (extended_call_layout layout callee fn.(fn_args))
      (CallFrame callee fn.(fn_body) result) ef result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    [Hheap Htyped [Hcallee Hargsloc] Hframes] Hvalues Hcode Hglobals Hbodies Hsource.
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  eapply runtime_primitive_call_entry; eauto.
Qed.

Print Assumptions evaluated_arguments_effect_nil.
Print Assumptions direct_application_components.
Print Assumptions direct_application_configuration_entry.
