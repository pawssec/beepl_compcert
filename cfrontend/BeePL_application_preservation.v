(* Every transition of an evaluated supported direct call preserves its full
   configuration, including the permitted argument-list identity transition. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_callable_entry BeePL_call_state.
Require Import BeePL_runtime_frames BeePL_frame_free BeePL_application_configuration.
Require Import BeePL_call_determinism.
Import ListNotations.

Theorem direct_application_configuration_preservation :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    m' caller' e',
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  primitive_internal_code_contract bge globals Sigma ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  (forall b fn, Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (callable_heap_locations bge layout) fn.(fn_body)) ->
  (forall fn, Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) ->
    frame_free fn.(fn_body)) ->
  ssem_expr bge p caller m
    (App (Val v (Ftype args effects result variadic)) es result) m' caller' e' ->
  caller' = caller /\ exists Sigma' layout',
    callable_heap_evolution bge Sigma layout Sigma' m' layout' /\
    primitive_internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller' m' layout' e' ef result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    m' caller' e' Hinitial Hvalues Hcode Hglobals Hbodies Hsource Hstep.
  pose proof Hinitial as Hparts.
  destruct Hparts as [Hheap Htyped [Hcallee Hargsloc] Hframes].
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  destruct (located_function_value bge Gamma Sigma layout v
    (Ftype args effects result variadic) nil args effects result variadic Hfunction Hcallee)
    as [b [fn [Hv [Hannotation [Hnil [Hfind Hsignature]]]]]]. subst v.
  destruct (Hcode b fn Hfind) as [Hfn Hparams].
  assert (Hargs_fn : type_exprs bge.(genv_cenv) Gamma Sigma es nil (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Harguments. }
  assert (Hshapes : Forall2 (fun param value => exists pt,
    snd param = Vtype pt /\ typeof_value value (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    (fn_args fn) (extract_values_exprs es)).
  { eapply primitive_evaluated_arguments; eauto. }
  destruct (direct_application_configuration_entry bge Gamma globals Sigma p caller m layout
    (Vloc b Ptrofs.zero) args effects result variadic es effects
    Hinitial Hvalues Hcode Hglobals Hbodies Hsource)
    as [chosen [callee [initialized [Sigma' [Hentry [Hupdate [Hcode' Hfinal]]]]]]].
  destruct (evaluated_application_entry_unique bge p caller m b
    (Ftype args effects result variadic) es result fn callee (fn_body chosen) initialized
    Hfind Hvalues Hshapes Hentry m' caller' e' Hstep)
    as [Hcaller Hcases]. subst caller'. split; [reflexivity |].
  destruct Hcases as [[Hm He] | [Hm He]]; subst m' e'.
  - exists Sigma, layout. split.
    + eapply callable_heap_evolution_refl; exact Hheap.
    + split; assumption.
  - exists Sigma', (extended_call_layout layout callee (fn_args chosen)).
    split; [exact Hupdate |]. split; assumption.
Qed.

Print Assumptions direct_application_configuration_preservation.
