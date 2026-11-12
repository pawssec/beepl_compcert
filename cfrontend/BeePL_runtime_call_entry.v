(* Entry establishes recursive frame validity for source function bodies.
   The call's allocated heap is shared with, and preserves, suspended callers. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state BeePL_call_state BeePL_callable_entry.
Require Import BeePL_runtime_frames BeePL_frame_free.
Import ListNotations.

Lemma frame_free_runtime_frames : forall bge Sigma m layout e,
  frame_free e -> runtime_frames bge Sigma m layout e.
Proof.
  intros bge Sigma m layout e. induction e using expr_ind_rec;
    intros Hfree; simpl in *; try contradiction;
    try solve [intuition eauto];
    try solve [rewrite all_expr_locations_Forall, Forall_forall in *; eauto].
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto; rewrite all_expr_locations_Forall; apply Forall_forall;
    intros child Hin;
    match goal with IH : forall e, In e ?es -> _, Hall : all_expr_locations _ ?es |- _ =>
      apply IH; [exact Hin | rewrite all_expr_locations_Forall, Forall_forall in Hall; apply Hall; exact Hin]
    end.
Qed.

Theorem runtime_primitive_call_entry :
  forall bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects,
  primitive_internal_code_contract bge globals Sigma ->
  type_expr bge.(genv_cenv) Gamma Sigma (Val v annotation) fn_effects
    (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations bge layout) (Val v annotation) ->
  type_exprs bge.(genv_cenv) Gamma Sigma es argument_effects args ->
  Forall (fun e => exists value ty, e = Val value ty) es ->
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
      (extended_call_layout layout callee fn.(fn_args)) /\
    primitive_internal_code_contract bge globals Sigma' /\
    runtime_configuration bge Gamma Sigma' caller initialized
      (extended_call_layout layout callee fn.(fn_args))
      (CallFrame callee fn.(fn_body) result) effects result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects
    Hcode Hfunction Hlocated Harguments Hvalues Hcaller Hglobals Hbodies Hsource.
  destruct (typed_located_primitive_call_entry bge Gamma globals Sigma p caller m layout
    v annotation fn_effects args effects result variadic es argument_effects
    Hcode Hfunction Hlocated Harguments Hvalues Hcaller Hglobals Hbodies)
    as [fn [callee [initialized [Sigma'
      [Hstep [Hext [Hcode' [Hcaller' [Hcallee' [Htyping [Hlocations [Hfind Hbodytyped]]]]]]]]]]]].
  exists fn, callee, initialized, Sigma'. split; [exact Hstep |]. split.
  - destruct Hcaller' as [Hblocks Hmemory Hcontents Hbindings].
    constructor; try assumption. intros b ofs ty chunk Hentry. left; exact Hentry.
  - split; [exact Hcode' |]. constructor; try assumption.
    simpl. exists (bind_vars globals (fn_args fn)), effects.
    split; [exact Hcallee' |]. split; [exact Hbodytyped |].
    apply frame_free_runtime_frames. apply Hsource. exact Hfind.
Qed.

Print Assumptions frame_free_runtime_frames.
Print Assumptions runtime_primitive_call_entry.
