(* Binding layouts for initialized primitive and ordinary-reference parameters.
   The layout itself records slots; initialization is a separate obligation. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_soundness_variables.
Require Import BeePL_callable_variables BeePL_call_state BeePL_parameter_allocations.
Require Import BeePL_scalar_parameters BeePL_scalar_parameter_allocations.
Import ListNotations.

Definition scalar_parameter_layout (callee : vmap)
    (params : list (ident * type)) : scalar_layout :=
  fun b ofs ty chunk => exists id,
    In (id, ty) params /\ PTree.get id callee = Some (b, ty) /\
    ofs = Ptrofs.zero /\ chunk = scalar_parameter_chunk ty.

Definition extended_scalar_call_layout (old : scalar_layout) (callee : vmap)
    (params : list (ident * type)) : scalar_layout :=
  fun b ofs ty chunk => old b ofs ty chunk \/
    scalar_parameter_layout callee params b ofs ty chunk.

Lemma scalar_parameter_not_function : forall ty,
  scalar_parameter_type ty -> is_funtype ty = false.
Proof.
  intros ty [[[pt Hty] | [[bt [a Hty]] | [bt [a Hty]]]] Hvolatile];
    subst ty; reflexivity.
Qed.

Theorem callee_scalar_callable_variable_layout :
  forall bge Sigma Sigma' Gamma old params callee m allocated,
  callable_variable_layout Gamma Sigma bge empty_vmap old ->
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => scalar_parameter_type (snd param)) params ->
  store_context_extends Sigma Sigma' ->
  callable_variable_layout (bind_vars Gamma params) Sigma' bge callee
    (extended_scalar_call_layout old callee params).
Proof.
  intros bge Sigma Sigma' Gamma old params callee m allocated
    Hglobals Halloc Hnames Hscalars Hextends x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots x ty Hin) as [b [Hget Hrest]].
    eapply callable_variable_data with (b := b).
    + left; exact Hget.
    + apply heap_variable_scalar with (chunk := scalar_parameter_chunk ty).
      right. exists x. split; [exact Hin |]. split; [exact Hget |]. split; reflexivity.
    + apply scalar_parameter_not_function.
      rewrite Forall_forall in Hscalars. exact (Hscalars _ Hin).
  - assert (Habsent : PTree.get x callee = None).
    { eapply parameter_allocation_missing_lookup; eauto. }
    destruct (Hglobals x ty Hglobal) as [b Hlocation Hbinding Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
    + eapply callable_variable_data with (b := b); [| |exact Hnonfun].
      * destruct Hlocation as [Hlocal|[Hnone Hsymbol]].
        -- unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
        -- right. split; assumption.
      * eapply heap_variable_binding_extend; [exact Hextends| |exact Hbinding].
        intros block ofs t chunk Hentry. left; exact Hentry.
    + eapply callable_variable_code; eauto.
    + unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
Qed.

Theorem caller_scalar_callable_variable_layout_extended :
  forall Gamma Sigma Sigma' bge caller old callee params,
  store_context_extends Sigma Sigma' ->
  callable_variable_layout Gamma Sigma bge caller old ->
  callable_variable_layout Gamma Sigma' bge caller
    (extended_scalar_call_layout old callee params).
Proof.
  intros. eapply callable_variable_layout_extend; [eassumption| |eassumption].
  intros b ofs ty chunk Hentry. left; exact Hentry.
Qed.

Print Assumptions callee_scalar_callable_variable_layout.
Print Assumptions caller_scalar_callable_variable_layout_extended.
