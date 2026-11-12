(* All evaluated calls with code parameters take the dedicated entry rule.
   The data-only rule cannot store a function and argument stuttering is guarded. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs Coqlib.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs BeePL_strict_progress.
Require Import BeePL_call_parameters BeePL_call_determinism BeePL_value_parameter_bindings.
Require Import BeePL_function_parameters.
Import ListNotations.

Lemma evaluated_code_application_step_cases :
  forall (ge : genv) p caller m b offset annotation es ret fn final caller' e',
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b offset)) = Some (Internal fn) ->
  has_function_parameter (fn_args fn) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  ssem_expr ge p caller m (App (Val (Vloc b offset) annotation) es ret) final caller' e' ->
  caller' = caller /\ exists codes data values callee Sigma Sigma' allocated,
    function_parameter_partition ge (fn_args fn) (extract_values_exprs es) codes data values /\
    alloc_variables ge Sigma codes m data callee allocated Sigma' /\
    bind_variables ge callee allocated data values final /\
    list_norepet (seq.unzip1 (fn_args fn)) /\ e' = CallFrame callee (fn_body fn) ret.
Proof.
  intros ge p caller m b offset annotation es ret fn final caller' e' Hfind Hhas Hvalues Hstep.
  pose proof (all_value_arguments_is_values es Hvalues) as Hready.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - congruence.
  - assert (fd = fn) by congruence. subst fd.
    exfalso. eapply function_parameters_cannot_use_data_binding; eauto.
  - assert (fd = fn) by congruence. subst fd.
    split; [reflexivity|]. do 7 eexists. repeat split; eauto.
Qed.

Theorem evaluated_code_application_entry_unique :
  forall (ge : genv) p caller m b offset annotation es ret fn codes data values
    callee AllocSigma allocated AllocSigma' initialized cenv ValueSigma L,
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b offset)) = Some (Internal fn) ->
  has_function_parameter (fn_args fn) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  function_parameter_partition ge (fn_args fn) (extract_values_exprs es) codes data values ->
  NoDup (map fst (fn_args fn)) ->
  call_parameter_values cenv ValueSigma L data values ->
  alloc_variables ge AllocSigma codes m data callee allocated AllocSigma' ->
  bind_variables ge callee allocated data values initialized ->
  forall final caller' e',
  ssem_expr ge p caller m (App (Val (Vloc b offset) annotation) es ret) final caller' e' ->
  caller' = caller /\ final = initialized /\ e' = CallFrame callee (fn_body fn) ret.
Proof.
  intros ge p caller m b offset annotation es ret fn codes data values
    callee AllocSigma allocated AllocSigma' initialized cenv ValueSigma L
    Hfind Hhas Hvalues Hpartition Hnames Hdata Halloc Hbind final caller' e' Hstep.
  destruct (evaluated_code_application_step_cases _ _ _ _ _ _ _ _ _ _ _ _ _ Hfind Hhas Hvalues Hstep)
    as [Hcaller [codes' [data' [values' [callee' [Sigma [Sigma' [allocated'
      [Hpartition' [Halloc' [Hbind' [Hnames' Hframe]]]]]]]]]]]].
  destruct (function_partition_unique _ _ _ _ _ _ Hpartition _ _ _ Hpartition')
    as [Hcodes [Hparams Hvals]]. subst codes' data' values'.
  destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ Halloc _ _ _ _ Halloc')
    as [Hcallee Hallocated]. subst callee' allocated'.
  assert (Hinputs : call_parameter_inputs cenv ValueSigma L callee allocated data values).
  { eapply allocated_call_parameter_inputs; eauto using function_partition_data_names. }
  assert (Hfinal : final = initialized) by (eapply call_parameter_binding_unique; eauto).
  repeat split; assumption.
Qed.

Print Assumptions evaluated_code_application_step_cases.
Print Assumptions evaluated_code_application_entry_unique.
