(* Evaluated calls with unit or supported scalar parameters preserve
   their runtime configuration. Only the selected signature is constrained. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_runtime_frames BeePL_frame_free.
Require Import BeePL_application_configuration BeePL_code_contracts.
Require Import BeePL_scalar_parameters BeePL_scalar_arguments BeePL_scalar_call_layout.
Require Import BeePL_call_parameters BeePL_call_parameter_layout BeePL_parameter_runtime_entry.
Require Import BeePL_value_parameter_bindings BeePL_call_determinism.
Import ListNotations.

Theorem parameter_call_preparation_unique :
  forall bge AllocSigma m params values callee allocated AllocSigma' final cenv Sigma L,
  alloc_variables bge AllocSigma empty_vmap m params callee allocated AllocSigma' ->
  call_parameter_inputs cenv Sigma L callee allocated params values ->
  bind_variables bge callee allocated params values final ->
  forall OtherSigma other_callee other_allocated OtherSigma' other_final,
  alloc_variables bge OtherSigma empty_vmap m params other_callee other_allocated OtherSigma' ->
  bind_variables bge other_callee other_allocated params values other_final ->
  other_callee = callee /\ other_allocated = allocated /\ other_final = final.
Proof.
  intros bge AllocSigma m params values callee allocated AllocSigma' final cenv Sigma L
    Halloc Hinputs Hbind OtherSigma other_callee other_allocated OtherSigma' other_final Hother Hotherbind.
  destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ Halloc
    _ _ _ _ Hother) as [Hmap Hmemory]. subst other_callee other_allocated.
  split; [reflexivity|]. split; [reflexivity|].
  eapply call_parameter_binding_unique; eauto.
Qed.

Theorem evaluated_parameter_application_entry_unique :
  forall (bge : genv) p caller m b annotation es ret fn callee body initialized cenv Sigma L,
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  call_parameter_values cenv Sigma L fn.(fn_args) (extract_values_exprs es) ->
  ssem_expr bge p caller m (App (Val (Vloc b Ptrofs.zero) annotation) es ret)
    initialized caller (CallFrame callee body ret) ->
  forall m' caller' e',
  ssem_expr bge p caller m (App (Val (Vloc b Ptrofs.zero) annotation) es ret)
    m' caller' e' ->
  caller' = caller /\
  ((m' = m /\ e' = App (Val (Vloc b Ptrofs.zero) annotation) es ret) \/
   (m' = initialized /\ e' = CallFrame callee body ret)).
Proof.
  intros bge p caller m b annotation es ret fn callee body initialized cenv ValueSigma L
    Hfn Hvalues Hshapes Hentry m' caller' e' Hstep.
  assert (Hnofun : ~ has_function_parameter (fn_args fn)).
  { eapply parameter_shapes_exclude_functions; [exact Hshapes |].
    intros param value [[Hunit | Hscalar] Hrest].
    - rewrite Hunit; reflexivity.
    - destruct Hscalar as [[[pt Hty] | [[bt [attr Hty]] | [bt [attr Hty]]]] Hvolatile]; rewrite Hty; reflexivity. }
  assert (Hdata : forall target,
    Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal target) ->
    ~ has_function_parameter (fn_args target)).
  { intros target Hfind. assert (target = fn) by congruence. subst target. exact Hnofun. }
  destruct (evaluated_application_step_cases _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hdata Hentry)
    as [_ [firstfn [firstcallee [Sigma [Sigma' [allocated
      [Hfirstfn [Halloc [Hbind [Hnames Hframe]]]]]]]]]].
  assert (firstfn = fn) by congruence. subst firstfn.
  inversion Hframe; subst firstcallee body.
  destruct (evaluated_application_step_cases _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hdata Hstep)
    as [Hcaller [otherfn [othercallee [OtherSigma [OtherSigma' [otherallocated
      [Hotherfn [Hotheralloc [Hotherbind [Hothernames Hotherframe]]]]]]]]]].
  split; [exact Hcaller |].
  right. assert (otherfn = fn) by congruence. subst otherfn.
    assert (Hinputs : call_parameter_inputs cenv ValueSigma L callee allocated (fn_args fn) (extract_values_exprs es)).
    { eapply allocated_call_parameter_inputs; eauto using call_parameter_names_nodup. }
    destruct (parameter_call_preparation_unique _ _ _ _ _ _ _ _ _ cenv ValueSigma L Halloc Hinputs Hbind
      _ _ _ _ _ Hotheralloc Hotherbind) as [Hmap [Hmem Hfinal]].
    subst othercallee. split; assumption.
Qed.

Print Assumptions evaluated_parameter_application_entry_unique.


Theorem direct_parameter_application_configuration_entry :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef,
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract bge globals Sigma ->
  Forall call_parameter_type args ->
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
      (extended_parameter_call_layout layout callee fn.(fn_args)) /\
    internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller initialized
      (extended_parameter_call_layout layout callee fn.(fn_args))
      (CallFrame callee fn.(fn_body) result) ef result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    [Hheap Htyped [Hcallee Hargsloc] Hframes] Hvalues Hcode Hscalar Hglobals Hbodies Hsource.
  destruct (direct_application_components _ _ _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [Hef [Hfunction Harguments]]. subst ef.
  eapply runtime_parameter_call_entry; eauto.
Qed.

Print Assumptions direct_parameter_application_configuration_entry.

Theorem direct_parameter_application_configuration_preservation :
  forall bge Gamma globals Sigma p caller m layout v args effects result variadic es ef
    m' caller' e',
  runtime_configuration bge Gamma Sigma caller m layout
    (App (Val v (Ftype args effects result variadic)) es result) ef result ->
  Forall (fun e => exists value annotation, e = Val value annotation) es ->
  internal_code_contract bge globals Sigma ->
  Forall call_parameter_type args ->
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
  assert (Hscalar_fn : Forall call_parameter_type (seq.unzip2 (fn_args fn))).
  { unfold type_of_function in Hsignature. inversion Hsignature; subst. exact Hscalar. }
  assert (Hfacts : call_parameter_values bge.(genv_cenv) Sigma
    (callable_heap_locations bge layout) (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_call_arguments; eauto. }
  destruct (direct_parameter_application_configuration_entry bge Gamma globals Sigma p caller m layout
    (Vloc b Ptrofs.zero) args effects result variadic es effects
    Hinitial Hvalues Hcode Hscalar Hglobals Hbodies Hsource)
    as [chosen [callee [initialized [Sigma' [Hentry [Hupdate [Hcode' Hfinal]]]]]]].
  destruct (evaluated_parameter_application_entry_unique bge p caller m b
    (Ftype args effects result variadic) es result fn callee (fn_body chosen) initialized
    bge.(genv_cenv) Sigma (callable_heap_locations bge layout)
    Hfind Hvalues Hfacts Hentry m' caller' e' Hstep)
    as [Hcaller Hcases]. subst caller'. split; [reflexivity |].
  destruct Hcases as [[Hm He] | [Hm He]]; subst m' e'.
  - exists Sigma, layout. split.
    + eapply callable_heap_evolution_refl; exact Hheap.
    + split; assumption.
  - exists Sigma', (extended_parameter_call_layout layout callee (fn_args chosen)).
    split; [exact Hupdate |]. split; assumption.
Qed.

Print Assumptions direct_parameter_application_configuration_preservation.
