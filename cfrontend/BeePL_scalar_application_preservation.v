(* Evaluated calls with primitive or ordinary-reference parameters preserve
   their runtime configuration. Only the selected signature is constrained. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_runtime_frames BeePL_frame_free.
Require Import BeePL_application_configuration BeePL_code_contracts.
Require Import BeePL_scalar_parameters BeePL_scalar_arguments BeePL_scalar_call_layout.
Require Import BeePL_scalar_runtime_entry BeePL_scalar_call_determinism.
Import ListNotations.

Theorem direct_scalar_application_configuration_entry :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef,
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract bge globals Sigma ->
  Forall scalar_parameter_type args ->
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
      (extended_scalar_call_layout layout callee fn.(fn_args)) /\
    internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller initialized
      (extended_scalar_call_layout layout callee fn.(fn_args))
      (CallFrame callee fn.(fn_body) result) ef result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    [Hheap Htyped [Hcallee Hargsloc] Hframes] Hvalues Hcode Hscalar Hglobals Hbodies Hsource.
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  eapply runtime_scalar_call_entry; eauto.
Qed.

Print Assumptions direct_scalar_application_configuration_entry.

Theorem direct_scalar_application_configuration_preservation :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    m' caller' e',
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract bge globals Sigma ->
  Forall scalar_parameter_type args ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  (forall b fn, Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (callable_heap_locations bge layout) fn.(fn_body)) ->
  (forall fn, Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) ->
    frame_free fn.(fn_body)) ->
  ssem_expr bge p caller m
    (App (Val v (Ftype args effects result variadic)) es result) m' caller' e' ->
  caller' = caller /\ exists Sigma' layout',
    callable_heap_evolution bge Sigma layout Sigma' m' layout' /\
    internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller' m' layout' e' ef result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    m' caller' e' Hinitial Hvalues Hcode Hscalar Hglobals Hbodies Hsource Hstep.
  pose proof Hinitial as Hparts.
  destruct Hparts as [Hheap Htyped [Hcallee Hargsloc] Hframes].
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  destruct (located_function_value bge Gamma Sigma layout v
    (Ftype args effects result variadic) nil args effects result variadic Hfunction Hcallee)
    as [b [fn [Hv [Hannotation [Hnil [Hfind Hsignature]]]]]]. subst v.
  assert (Hargs_fn : type_exprs bge.(genv_cenv) Gamma Sigma es nil (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Harguments. }
  assert (Hscalar_fn : Forall scalar_parameter_type (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Hscalar. }
  assert (Hfacts : scalar_parameter_values bge.(genv_cenv) Sigma
    (callable_heap_locations bge layout) (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_scalar_arguments; eauto. }
  destruct (direct_scalar_application_configuration_entry bge Gamma globals Sigma p caller m layout
    (Vloc b Ptrofs.zero) args effects result variadic es effects
    Hinitial Hvalues Hcode Hscalar Hglobals Hbodies Hsource)
    as [chosen [callee [initialized [Sigma' [Hentry [Hupdate [Hcode' Hfinal]]]]]]].
  destruct (evaluated_scalar_application_entry_unique bge p caller m b
    (Ftype args effects result variadic) es result fn callee (fn_body chosen) initialized
    bge.(genv_cenv) Sigma (callable_heap_locations bge layout)
    Hfind Hvalues Hfacts Hentry m' caller' e' Hstep)
    as [Hcaller Hcases]. subst caller'. split; [reflexivity |].
  destruct Hcases as [[Hm He] | [Hm He]]; subst m' e'.
  - exists Sigma, layout. split.
    + eapply callable_heap_evolution_refl; exact Hheap.
    + split; assumption.
  - exists Sigma', (extended_scalar_call_layout layout callee (fn_args chosen)).
    split; [exact Hupdate |]. split; assumption.
Qed.

Print Assumptions direct_scalar_application_configuration_preservation.
