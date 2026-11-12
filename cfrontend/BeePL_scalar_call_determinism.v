(* Arbitrary evaluated call steps agree with the constructed scalar/reference
   entry, except for the explicit argument-list identity step. *)
Require Import List ZArith Coqlib AST Maps Memory Ctypes Integers Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_runtime_locations BeePL_call_determinism.
Require Import BeePL_scalar_parameters BeePL_scalar_arguments.
Require Import BeePL_scalar_parameter_allocations BeePL_scalar_parameter_bindings.
Import ListNotations.

Theorem scalar_call_preparation_unique :
  forall bge AllocSigma m params values callee allocated AllocSigma' final cenv Sigma L,
  alloc_variables bge AllocSigma empty_vmap m params callee allocated AllocSigma' ->
  scalar_parameter_inputs cenv Sigma L callee allocated params values ->
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
  eapply scalar_parameter_binding_unique; eauto.
Qed.

Lemma actual_scalar_allocation_inputs :
  forall bge AllocSigma m params values callee allocated AllocSigma' cenv Sigma L,
  alloc_variables bge AllocSigma empty_vmap m params callee allocated AllocSigma' ->
  NoDup (map fst params) ->
  scalar_parameter_values cenv Sigma L params values ->
  scalar_parameter_inputs cenv Sigma L callee allocated params values.
Proof.
  intros bge AllocSigma m params values callee allocated AllocSigma' cenv Sigma L
    Halloc Hnames Hvalues.
  assert (Htypes : Forall (fun param => scalar_parameter_type (snd param)) params).
  { clear - Hvalues. induction Hvalues; constructor; tauto. }
  destruct (scalar_parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames Htypes)
    as [Hslots Hdistinct].
  assert (Hbuild : forall ps vs,
    scalar_parameter_values cenv Sigma L ps vs ->
    (forall param, In param ps -> In param params) ->
    scalar_parameter_inputs cenv Sigma L callee allocated ps vs).
  { intros ps vs Hfacts. induction Hfacts; intros Hincluded; constructor.
    - destruct x as [id ty]. destruct H as [Hscalar [Htyped Hlocated]].
      destruct (Hslots id ty (Hincluded _ (or_introl eq_refl)))
        as [b [Hget [Hfresh [Hvalid Haccess]]]].
      exists b. simpl in *. split; [exact Hget|]. split; [exact Hscalar|].
      split; [exact Htyped|]. split; assumption.
    - apply IHHfacts. intros param Hin. apply Hincluded. right; exact Hin. }
  apply Hbuild; [exact Hvalues|auto].
Qed.

Theorem evaluated_scalar_application_entry_unique :
  forall (bge : genv) p caller m b annotation es ret fn callee body initialized cenv Sigma L,
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  scalar_parameter_values cenv Sigma L fn.(fn_args) (extract_values_exprs es) ->
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
    intros param value [Hkind Hrest].
    destruct Hkind as [[[pt Hty] | [[bt [attr Hty]] | [bt [attr Hty]]]] Hvolatile]; rewrite Hty; reflexivity. }
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
    assert (Hinputs : scalar_parameter_inputs cenv ValueSigma L callee allocated (fn_args fn) (extract_values_exprs es)).
    { eapply actual_scalar_allocation_inputs; eauto using call_parameter_names_nodup. }
    destruct (scalar_call_preparation_unique _ _ _ _ _ _ _ _ _ cenv ValueSigma L Halloc Hinputs Hbind
      _ _ _ _ _ Hotheralloc Hotherbind) as [Hmap [Hmem Hfinal]].
    subst othercallee. split; assumption.
Qed.

Print Assumptions evaluated_scalar_application_entry_unique.
