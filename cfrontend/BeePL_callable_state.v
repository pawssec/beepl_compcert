(* Callable-aware state integration for initialized primitive call parameters. *)
Require Import List ZArith Coqlib Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_allocation_proofs BeePL_call_bindings BeePL_parameter_allocations.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_variables.
Require Import BeePL_call_state BeePL_call_memory BeePL_call_entry.
Require Import BeePL_callable_locations BeePL_callable_variables.
Import ListNotations.

Record callable_heap_state (Gamma : ty_context) (Sigma : store_context)
    (bge : genv) (vm : vmap) (m : Mem.mem) (layout : scalar_layout) : Prop := {
  callable_state_blocks : store_blocks_valid Sigma m;
  callable_state_memory : typed_memory_layout bge.(genv_cenv) Sigma layout m;
  callable_state_contents : memory_locations (callable_heap_locations bge layout) layout m;
  callable_state_bindings : callable_variable_layout Gamma Sigma bge vm layout
}.

Theorem callee_callable_variable_layout :
  forall bge Sigma Sigma' Gamma old params callee m allocated,
  callable_variable_layout Gamma Sigma bge empty_vmap old ->
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => exists pt, snd param = Vtype pt) params ->
  store_context_extends Sigma Sigma' ->
  callable_variable_layout (bind_vars Gamma params) Sigma' bge callee
    (extended_call_layout old callee params).
Proof.
  intros bge Sigma Sigma' Gamma old params callee m allocated
    Hglobals Halloc Hnames Hprimitive Hextends x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - rewrite Forall_forall in Hprimitive.
    destruct (Hprimitive (x, ty) Hin) as [pt Hty]. simpl in Hty. subst ty.
    destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
      as [Hslots Hdistinct].
    destruct (Hslots x (Vtype pt) Hin) as [b [Hget Hrest]].
    eapply callable_variable_data with (b := b).
    + left; exact Hget.
    + apply heap_variable_scalar with (chunk := chunk_of_ptype pt).
      right. exists x, pt. repeat split; assumption.
    + reflexivity.
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

Theorem caller_callable_variable_layout_extended :
  forall Gamma Sigma Sigma' bge caller old callee params,
  store_context_extends Sigma Sigma' ->
  callable_variable_layout Gamma Sigma bge caller old ->
  callable_variable_layout Gamma Sigma' bge caller (extended_call_layout old callee params).
Proof.
  intros. eapply callable_variable_layout_extend; [eassumption| |eassumption].
  intros b ofs ty chunk Hentry. left; exact Hentry.
Qed.

Theorem primitive_callable_state_preparation :
  forall bge Gamma globals Sigma caller m layout params values,
  NoDup (map fst params) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params values ->
  callable_heap_state Gamma Sigma bge caller m layout ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\
    callable_heap_state Gamma Sigma' bge caller initialized
      (extended_call_layout layout callee params) /\
    callable_heap_state (bind_vars globals params) Sigma' bge callee initialized
      (extended_call_layout layout callee params).
Proof.
  intros bge Gamma globals Sigma caller m layout params values
    Hnames Hshapes [Hblocks Hmemory Hlocations Hbindings] Hglobals.
  destruct (primitive_call_storage_preparation bge Sigma m params values
    bge.(genv_cenv) layout Hnames Hshapes Hblocks Hmemory)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hblocks' [Hmemory' [Hcells Hfresh]]]]]]]]]].
  assert (Hprimitive : Forall (fun param => exists pt, snd param = Vtype pt) params).
  { clear - Hshapes. induction Hshapes; constructor; auto. destruct H as [pt [Ht Hrest]]. eauto. }
  assert (Hmemory_all : typed_memory_layout bge.(genv_cenv) Sigma'
    (extended_call_layout layout callee params) initialized).
  { intros b ofs ty chunk [Hold | [id [pt [Hin [Hget [Hofs [Hty Hchunk]]]]]]].
    - apply Hmemory'; exact Hold.
    - subst ofs ty chunk. eapply Hcells; eauto. }
  assert (Hlocations_old : memory_locations (callable_heap_locations bge layout)
    layout initialized).
  { eapply parameter_preparation_memory_locations; eauto. }
  assert (Hlocation_inc : location_context_includes
    (callable_heap_locations bge layout)
    (callable_heap_locations bge (extended_call_layout layout callee params))).
  { apply callable_heap_locations_monotone. intros b ofs ty chunk Hentry. left; exact Hentry. }
  assert (Hlocations_all : memory_locations
    (callable_heap_locations bge (extended_call_layout layout callee params))
    (extended_call_layout layout callee params) initialized).
  { intros b ofs ty chunk [Hold | [id [pt [Hin [Hget [Hofs [Hty Hchunk]]]]]]] v Hread.
    - eapply value_locations_monotone; [exact Hlocation_inc |].
      eapply Hlocations_old; eauto.
    - subst ofs ty chunk. apply primitive_value_locations.
      eapply declarative_value_shape with (Gamma := empty_context).
      eapply typed_memory_cell_read_preservation; [eapply Hcells; eauto | exact Hread]. }
  exists callee, allocated, initialized, Sigma'.
  split; [exact Halloc |]. split; [exact Hbind |]. split; [exact Hext |]. split.
  - constructor; try assumption.
    eapply caller_callable_variable_layout_extended; eauto.
  - constructor; try assumption.
    eapply callee_callable_variable_layout; eauto.
Qed.

Print Assumptions primitive_callable_state_preparation.

Theorem callable_state_variable_progress : forall Gamma Sigma bge vm m layout p x ty ef,
  callable_heap_state Gamma Sigma bge vm m layout ->
  type_expr bge.(genv_cenv) Gamma Sigma (Var x ty) ef ty ->
  exists v,
    ssem_expr bge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v ty) ef ty /\
    runtime_locations (callable_heap_locations bge layout) (Val v ty).
Proof.
  intros Gamma Sigma bge vm m layout p x ty ef Hstate Htyped.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  inversion Htyped; subst. eapply callable_variable_progress; eauto.
Qed.

Theorem callable_state_variable_preservation :
  forall Gamma Sigma bge vm m layout p x ty ef m' vm' e',
  callable_heap_state Gamma Sigma bge vm m layout ->
  type_expr bge.(genv_cenv) Gamma Sigma (Var x ty) ef ty ->
  ssem_expr bge p vm m (Var x ty) m' vm' e' ->
  callable_heap_state Gamma Sigma bge vm' m' layout /\
  type_expr bge.(genv_cenv) Gamma Sigma e' ef ty /\
  runtime_locations (callable_heap_locations bge layout) e'.
Proof.
  intros Gamma Sigma bge vm m layout p x ty ef m' vm' e' Hstate Htyped Hstep.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  inversion Htyped; subst.
  assert (Hresult : m' = m /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations (callable_heap_locations bge layout) e').
  { eapply callable_variable_preservation; eauto. }
  destruct Hresult as [Hm [Hvm [Htype Hloc]]]. subst m' vm'.
  split; [constructor; assumption |]. split; assumption.
Qed.

Print Assumptions callable_state_variable_progress.
Print Assumptions callable_state_variable_preservation.

