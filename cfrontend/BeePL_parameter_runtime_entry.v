(* Constructive runtime entry for unit, primitive and reference arguments.
   Supported storage is checked at this call site; the global code contract
   asserts body typing without imposing a primitive-only program signature. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_callable_entry BeePL_call_entry.
Require Import BeePL_runtime_frames BeePL_frame_free BeePL_runtime_call_entry.
Require Import BeePL_code_contracts BeePL_scalar_parameters BeePL_scalar_arguments.
Require Import BeePL_call_parameters BeePL_call_parameter_layout BeePL_parameter_call_preparation.
Import ListNotations.

Theorem runtime_parameter_call_entry :
  forall bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects,
  internal_code_contract bge globals Sigma ->
  type_expr bge.(genv_cenv) Gamma Sigma (Val v annotation) fn_effects
    (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations bge layout) (Val v annotation) ->
  type_exprs bge.(genv_cenv) Gamma Sigma es argument_effects args ->
  Forall (fun e => exists value ty, e = Val value ty) es ->
  all_expr_locations (runtime_locations (callable_heap_locations bge layout)) es ->
  Forall call_parameter_type args ->
  callable_heap_state Gamma Sigma bge caller m layout ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  (forall b fn, Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (callable_heap_locations bge layout) fn.(fn_body)) ->
  (forall fn, Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) ->
    frame_free fn.(fn_body)) ->
  exists fn callee initialized Sigma',
    ssem_expr bge p caller m (App (Val v annotation) es result)
      initialized caller (CallFrame callee fn.(fn_body) result) /\
    callable_heap_evolution bge Sigma layout Sigma' initialized
      (extended_parameter_call_layout layout callee fn.(fn_args)) /\
    internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller initialized
      (extended_parameter_call_layout layout callee fn.(fn_args))
      (CallFrame callee fn.(fn_body) result) effects result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects Hcode Hfunction Hlocation
    Harguments Hvalues Harglocations Hscalar Hcaller Hglobals Hbodies Hsource.
  destruct (located_function_value _ _ _ _ _ _ _ _ _ _ _ Hfunction Hlocation)
    as [b [fn [Hv [Hannotation [Hef [Hfind Hsignature]]]]]].
  subst v annotation fn_effects.
  pose proof (Hcode b fn Hfind) as Hfn.
  unfold type_of_function in Hsignature. inversion Hsignature; subst args effects result variadic.
  assert (Hfacts : call_parameter_values bge.(genv_cenv) Sigma
    (callable_heap_locations bge layout) (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_call_arguments; eauto. }
  assert (Htypes : typeof_exprs es = seq.unzip2 (fn_args fn)) by
    (eapply typed_arguments_annotations; eauto).
  inversion Hfn; subst.
  assert (Hnames : NoDup (map fst (fn_args fn))) by
    (apply parameter_names_nodup; assumption).
  destruct (parameter_callable_state_preparation bge Gamma globals Sigma caller m layout
    (fn_args fn) (extract_values_exprs es) Hnames Hfacts Hcaller Hglobals)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hcaller' Hcallee']]]]]]]].
  assert (Hbodytyped : type_expr bge.(genv_cenv) (bind_vars globals (fn_args fn)) Sigma'
    (fn_body fn) (fn_effect fn) (fn_return fn)).
  { eapply (proj2 typing_store_extension); eauto. }
  exists fn, callee, initialized, Sigma'. split.
  - rewrite <- Htypes. eapply ssem_app3; eauto; reflexivity.
  - split.
    + destruct Hcaller' as [Hblocks Hmemory Hcontents Hbindings].
      constructor; try assumption. intros block ofs ty chunk Hentry. left; exact Hentry.
    + split.
      * eapply internal_code_contract_store_extension; eauto.
      * constructor; [exact Hcaller' | | |].
        -- eapply ty_callframe; exact Hbodytyped.
        -- simpl. eapply runtime_locations_monotone; [|apply (Hbodies b fn Hfind)].
           apply callable_heap_locations_monotone.
           intros block ofs ty chunk Hentry. left; exact Hentry.
        -- simpl. exists (bind_vars globals (fn_args fn)), (fn_effect fn).
           split; [exact Hcallee' |]. split; [exact Hbodytyped |].
           apply frame_free_runtime_frames. apply Hsource. exact Hfind.
Qed.

Print Assumptions runtime_parameter_call_entry.
