(* Constructive entry into internal calls with primitive parameters.  This
   proves allocation and initialization exist; it does not assume successful
   binding, a callable-value typing rule, or a callee-body progress theorem. *)
Require Import List ZArith Coqlib Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL_aux BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_allocation_proofs BeePL_call_bindings BeePL_parameter_allocations.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_variables.
Require Import BeePL_soundness_state BeePL_call_state BeePL_call_memory.
Import ListNotations.

Lemma parameter_names_nodup : forall (params : list (ident * type)),
  list_norepet (seq.unzip1 params) -> NoDup (map fst params).
Proof.
  induction params as [|[id ty] params IH]; simpl; intros H; inversion H; subst;
    constructor; auto.
Qed.

Theorem primitive_call_storage_preparation :
  forall bge Sigma m params values cenv layout,
  NoDup (map fst params) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params values ->
  store_blocks_valid Sigma m -> typed_memory_layout cenv Sigma layout m ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' initialized /\
    typed_memory_layout cenv Sigma' layout initialized /\
    (forall id pt b, In (id, Vtype pt) params ->
      PTree.get id callee = Some (b, Vtype pt) ->
      typed_memory_cell cenv Sigma' initialized b Ptrofs.zero
        (Vtype pt) (chunk_of_ptype pt)) /\
    (forall b, parameter_binding_target callee params b -> ~ Mem.valid_block m b).
Proof.
  intros bge Sigma m params values cenv layout Hnames Hshapes Hblocks Hmemory.
  destruct (allocate_primitive_parameters bge Sigma m params values Hnames Hshapes)
    as [callee [allocated [Sigma' [Halloc [Hinputs [Hdistinct Hfresh]]]]]].
  destruct (bind_primitive_parameters_total bge callee allocated params values Hinputs)
    as [initialized Hbind].
  destruct (alloc_variables_store_extension _ _ _ _ _ _ _ _ Halloc Hblocks)
    as [Hext Hallocated].
  exists callee, allocated, initialized, Sigma'.
  split; [exact Halloc |]. split; [exact Hbind |]. split; [exact Hext |].
  split.
  - intros b ty Hentry. eapply bind_parameters_valid_blocks; [exact Hbind |].
    eapply Hallocated; eauto.
  - split.
    + eapply bind_parameters_layout_frame; [exact Hbind | |].
      * eapply typed_memory_layout_context_extension; [|exact Hext].
        eapply alloc_variables_typed_memory_frame; eauto.
      * intros b ofs ty chunk Hcell Htarget. apply (Hfresh b Htarget).
        eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies;
          [exact (typed_cell_permission _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) | constructor].
    + split; [|exact Hfresh]. intros id pt b Hin Hlookup.
      eapply bind_primitive_parameters_initialized; eauto.
Qed.

(* The function lookup and exact signature remain explicit. They must later be
   supplied by the callable runtime invariant, not inferred from heap typing. *)
Theorem primitive_internal_call_entry :
  forall bge Gamma Sigma p caller m layout fd l ofs es,
  type_function bge.(genv_cenv) Gamma Sigma fd ->
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc l ofs)) = Some (Internal fd) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  typeof_exprs es = seq.unzip2 fd.(fn_args) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    fd.(fn_args) (extract_values_exprs es) ->
  store_blocks_valid Sigma m -> typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  exists callee initialized Sigma',
    ssem_expr bge p caller m
      (App (Val (Vloc l ofs) (Ftype (typeof_exprs es) fd.(fn_effect)
        fd.(fn_return) (get_v_fundef (Internal fd)))) es fd.(fn_return))
      initialized caller (CallFrame callee fd.(fn_body) fd.(fn_return)) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' initialized /\
    typed_memory_layout bge.(genv_cenv) Sigma' layout initialized /\
    type_expr bge.(genv_cenv) Gamma Sigma'
      (CallFrame callee fd.(fn_body) fd.(fn_return)) fd.(fn_effect) fd.(fn_return) /\
    (forall id pt b, In (id, Vtype pt) fd.(fn_args) ->
      PTree.get id callee = Some (b, Vtype pt) ->
      typed_memory_cell bge.(genv_cenv) Sigma' initialized b Ptrofs.zero
        (Vtype pt) (chunk_of_ptype pt)).
Proof.
  intros bge Gamma Sigma p caller m layout fd l ofs es
    Hfunction Hfind Hvalues Htypes Hshapes Hblocks Hmemory.
  inversion Hfunction; subst.
  assert (Hnames : NoDup (map fst (fn_args fd))) by
    (apply parameter_names_nodup; assumption).
  destruct (primitive_call_storage_preparation bge Sigma m (fn_args fd)
    (extract_values_exprs es) bge.(genv_cenv) layout Hnames Hshapes Hblocks Hmemory)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hblocks' [Hmemory' [Hcells Hfresh]]]]]]]]]].
  exists callee, initialized, Sigma'. split.
  - eapply ssem_app3; eauto; reflexivity.
  - split; [exact Hext |]. split; [exact Hblocks' |]. split; [exact Hmemory' |].
    split; [|exact Hcells]. eapply ty_callframe.
    eapply (proj2 typing_store_extension); eauto.
Qed.

Print Assumptions primitive_call_storage_preparation.
Print Assumptions primitive_internal_call_entry.

Theorem primitive_call_state_preparation :
  forall bge Gamma globals Sigma caller m layout params values,
  NoDup (map fst params) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params values ->
  mixed_heap_state Gamma Sigma bge caller m layout ->
  mixed_variable_layout globals Sigma bge empty_vmap layout ->
  exists callee allocated initialized Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    bind_variables bge callee allocated params values initialized /\
    store_context_extends Sigma Sigma' /\
    mixed_heap_state Gamma Sigma' bge caller initialized
      (extended_call_layout layout callee params) /\
    mixed_heap_state (bind_vars globals params) Sigma' bge callee initialized
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
  assert (Hlocations_old : memory_locations (array_heap_locations bge.(genv_cenv) layout)
    layout initialized).
  { eapply parameter_preparation_memory_locations; eauto. }
  assert (Hlocation_inc : location_context_includes
    (array_heap_locations bge.(genv_cenv) layout)
    (array_heap_locations bge.(genv_cenv) (extended_call_layout layout callee params))).
  { apply array_heap_locations_monotone. intros b ofs ty chunk Hentry. left; exact Hentry. }
  assert (Hlocations_all : memory_locations
    (array_heap_locations bge.(genv_cenv) (extended_call_layout layout callee params))
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
    eapply caller_mixed_variable_layout_extended; eauto.
  - constructor; try assumption.
    eapply callee_mixed_variable_layout; eauto.
Qed.

Print Assumptions primitive_call_state_preparation.

Theorem primitive_internal_call_state_entry :
  forall bge Gamma globals Sigma p caller m layout fd l ofs es,
  type_function bge.(genv_cenv) globals Sigma fd ->
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc l ofs)) = Some (Internal fd) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  typeof_exprs es = seq.unzip2 fd.(fn_args) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    fd.(fn_args) (extract_values_exprs es) ->
  mixed_heap_state Gamma Sigma bge caller m layout ->
  mixed_variable_layout globals Sigma bge empty_vmap layout ->
  runtime_locations (array_heap_locations bge.(genv_cenv) layout) fd.(fn_body) ->
  exists callee initialized Sigma',
    ssem_expr bge p caller m
      (App (Val (Vloc l ofs) (Ftype (typeof_exprs es) fd.(fn_effect)
        fd.(fn_return) (get_v_fundef (Internal fd)))) es fd.(fn_return))
      initialized caller (CallFrame callee fd.(fn_body) fd.(fn_return)) /\
    store_context_extends Sigma Sigma' /\
    mixed_heap_state Gamma Sigma' bge caller initialized
      (extended_call_layout layout callee fd.(fn_args)) /\
    mixed_heap_state (bind_vars globals fd.(fn_args)) Sigma' bge callee initialized
      (extended_call_layout layout callee fd.(fn_args)) /\
    type_expr bge.(genv_cenv) (bind_vars globals fd.(fn_args)) Sigma'
      fd.(fn_body) fd.(fn_effect) fd.(fn_return) /\
    runtime_locations (array_heap_locations bge.(genv_cenv)
      (extended_call_layout layout callee fd.(fn_args)))
      (CallFrame callee fd.(fn_body) fd.(fn_return)).
Proof.
  intros bge Gamma globals Sigma p caller m layout fd l ofs es
    Hfunction Hfind Hvalues Htypes Hshapes Hcaller Hglobals Hbodyloc.
  inversion Hfunction; subst.
  assert (Hnames : NoDup (map fst (fn_args fd))) by
    (apply parameter_names_nodup; assumption).
  destruct (primitive_call_state_preparation bge Gamma globals Sigma caller m layout
    (fn_args fd) (extract_values_exprs es) Hnames Hshapes Hcaller Hglobals)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hcaller' Hcallee']]]]]]]].
  exists callee, initialized, Sigma'. split.
  - eapply ssem_app3; eauto; reflexivity.
  - split; [exact Hext |]. split; [exact Hcaller' |]. split; [exact Hcallee' |]. split.
    + eapply (proj2 typing_store_extension); eauto.
    + simpl. eapply runtime_locations_monotone; [|exact Hbodyloc].
      apply array_heap_locations_monotone. intros b off ty chunk Hentry. left; exact Hentry.
Qed.

Print Assumptions primitive_internal_call_state_entry.
