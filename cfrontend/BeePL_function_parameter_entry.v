Require Import BeePL_heap_extents BeePL_parameter_extents.
(* Function-valued arguments become authentic immutable code bindings. Data
   arguments alone allocate storage; all frames share the initialized heap. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_frame_free BeePL_code_contracts BeePL_call_entry BeePL_call_parameters.
Require Import BeePL_call_parameter_layout BeePL_coherent_parameters BeePL_aggregate_memory.
Require Import BeePL_object_coverage BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_function_parameters BeePL_function_parameter_storage BeePL_function_parameter_bindings.
Require Import BeePL_layout_coherence.
Require Import BeePL_callable_entry.
Require Import BeePL_initialized_call_entry.
Require Import BeePL_scalar_parameters BeePL_soundness_variables BeePL_call_state BeePL_parameter_allocations.
Require Import BeePL_scalar_call_layout BeePL_allocation_proofs.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.

Theorem function_parameter_packet_callee_bindings :
  forall ge Sigma Sigma' globals cells objects packets params values codes data data_values m callee allocated,
  function_parameter_partition ge params values codes data data_values ->
  NoDup (map fst params) ->
  Forall (fun param => call_parameter_type (snd param)) data ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  alloc_variables ge Sigma codes m data callee allocated Sigma' ->
  store_context_extends Sigma Sigma' ->
  packet_variable_layout (bind_vars globals params) Sigma' ge callee
    (extended_parameter_call_layout cells callee data) objects packets.
Proof.
  intros ge Sigma Sigma' globals cells objects packets params values codes data data_values m callee allocated
    Hpartition Hnames Htypes Hglobals Halloc Hext x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - apply packet_variable_callable. destruct (function_partition_parameter_origin _ _ _ _ _ _ Hpartition Hnames x ty Hin)
      as [Hdata|[b [Hget Hcode]]].
    + destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc
        (function_partition_data_names _ _ _ _ _ _ Hpartition Hnames)) as [Hslots Hdistinct].
      destruct (Hslots x ty Hdata) as [b [Hget Hrest]].
      rewrite Forall_forall in Htypes. specialize (Htypes _ Hdata). simpl in Htypes.
      destruct Htypes as [Hunit|Hscalar].
      * subst ty. eapply callable_variable_data with (b := b).
        -- left; exact Hget.
        -- apply heap_variable_unit.
        -- reflexivity.
      * eapply callable_variable_data with (b := b).
        -- left; exact Hget.
        -- apply heap_variable_scalar with (chunk := scalar_parameter_chunk ty).
           right. split; [exact Hscalar|]. exists x. split; [exact Hdata|].
           split; [exact Hget|]. split; reflexivity.
        -- apply scalar_parameter_not_function; exact Hscalar.
    + eapply callable_variable_local_code; [|exact Hcode].
      rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Halloc x).
      * exact Hget.
      * eapply function_partition_code_not_data; eauto.
  - assert (HmissingData : ~ In x (map fst data)).
    { intro Hin. apply Hmissing. apply in_map_iff in Hin as [[id t] [Heq Hin]].
      simpl in Heq; subst id. apply in_map_iff. exists (x,t). split; [reflexivity|].
      eapply function_partition_data_in; eauto. }
    assert (Habsent : PTree.get x callee = None).
    { rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Halloc x HmissingData).
      eapply function_partition_code_missing; eauto. }
    destruct (Hglobals x ty Hglobal) as [Hcall|b Hloc Hkind Hobject|b Hloc Hbytes Hpacket].
    2: { eapply packet_variable_aggregate; [|exact Hkind|exact Hobject].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]].
      - unfold empty_vmap in Hlocal; rewrite PTree.gempty in Hlocal; discriminate.
      - right; split; assumption. }
    2: { eapply packet_variable_bytes; [|exact Hbytes|exact Hpacket].
      destruct Hloc as [Hlocal|[Hnone Hsymbol]].
      - unfold empty_vmap in Hlocal; rewrite PTree.gempty in Hlocal; discriminate.
      - right; split; assumption. }
    apply packet_variable_callable.
    destruct Hcall as [b Hlocation Hbinding Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
    + eapply callable_variable_data with (b := b); [| |exact Hnonfun].
      * destruct Hlocation as [Hlocal|[Hnone Hsymbol]].
        -- unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
        -- right; split; assumption.
      * eapply heap_variable_binding_extend; [exact Hext| |exact Hbinding].
        intros block ofs t chunk Hentry. left; exact Hentry.
    + eapply callable_variable_code; eauto.
    + unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
Qed.



Lemma packet_code_or_data_values : forall ge Sigma cells objects packets params values,
  code_or_data_parameter_values ge Sigma (packet_heap_locations ge cells objects packets) params values ->
  code_or_data_parameter_values ge Sigma (descriptor_heap_locations ge cells objects) params values.
Proof.
  intros ge Sigma cells objects packets params values H. induction H; constructor; auto.
  destruct H as [Hsupported [Htyped Hlocated]]. repeat split; try assumption.
  eapply packet_value_locations_nonbytes; [|exact Hlocated].
  destruct Hsupported as [Hdata|Hcode].
  - destruct Hdata as [Hunit|[[[pt Heq]|[[bt [attr Heq]]|[bt [attr Heq]]]] Hvolatile]];
      congruence.
  - intro Heq. rewrite Heq in Hcode. discriminate.
Qed.

Theorem coherent_function_parameter_entry :
  forall (ge : genv) Gamma globals Sigma p caller m objects cells packets b fn es argument_effects,
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  internal_code_contract ge globals Sigma ->
  has_function_parameter (fn_args fn) ->
  type_exprs ge.(genv_cenv) Gamma Sigma es argument_effects (seq.unzip2 (fn_args fn)) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  all_expr_locations (runtime_locations (packet_heap_locations ge cells objects packets)) es ->
  Forall (fun ty => call_parameter_type ty \/ is_funtype ty = true) (seq.unzip2 (fn_args fn)) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  runtime_locations (packet_heap_locations ge cells objects packets) (fn_body fn) ->
  frame_free (fn_body fn) ->
  exists callee initialized Sigma' data,
    ssem_expr ge p caller m
      (App (Val (Vloc b Ptrofs.zero) (type_of_function fn)) es (fn_return fn))
      initialized caller (CallFrame callee (fn_body fn) (fn_return fn)) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' initialized objects
      (extended_parameter_call_layout cells callee data) packets /\
    internal_code_contract ge globals Sigma' /\
    coherent_runtime_configuration ge Gamma Sigma' caller initialized objects
      (extended_parameter_call_layout cells callee data) packets
      (CallFrame callee (fn_body fn) (fn_return fn)) (fn_effect fn) (fn_return fn) /\
    exists codes data_values allocated,
      function_parameter_partition ge (fn_args fn) (extract_values_exprs es) codes data data_values /\
      call_parameter_values ge.(genv_cenv) Sigma (descriptor_heap_locations ge cells objects) data data_values /\
      alloc_variables ge Sigma codes m data callee allocated Sigma' /\
      bind_variables ge callee allocated data data_values initialized.
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets b fn es argument_effects
    Hfind Hcode Hhas Harguments Hvalues Hlocations Htypes
    [Hblocks Hmemory Hcaller Hpackets Hextent] Hcoherent Hglobals Hbodylocations Hsource.
  pose proof (Hcode b fn Hfind) as Hfn.
  assert (Hfacts : code_or_data_parameter_values ge Sigma (packet_heap_locations ge cells objects packets)
    (fn_args fn) (extract_values_exprs es)).
  { eapply typed_located_code_or_data_arguments; eauto. }
  pose proof (packet_code_or_data_values _ _ _ _ _ _ _ Hfacts) as Hfacts_old.
  destruct (located_function_parameter_partition ge Sigma (descriptor_heap_locations ge cells objects)
    (fn_args fn) (extract_values_exprs es) ltac:(
      intros block args effects result variadic [Hcall|Hdescriptor];
      [exact Hcall|destruct Hdescriptor as [[Hkind _]|[basic [attr [Hbad _]]]]; discriminate]) Hfacts_old)
    as [codes [data [data_values [Hpartition Hdata]]]].
  inversion Hfn; subst.
  assert (Hnames : NoDup (map fst (fn_args fn))) by (apply parameter_names_nodup; assumption).
  assert (Hdatanames : NoDup (map fst data)) by (eapply function_partition_data_names; eauto).
  assert (Hdatatypes : Forall (fun param => call_parameter_type (snd param)) data).
  { clear - Hdata. induction Hdata; constructor; tauto. }
  destruct (mapped_initialized_object_parameter_preparation ge Sigma codes m objects cells data data_values
    Hdatanames Hdata Hblocks Hmemory)
    as [callee [allocated [initialized [Sigma' [Halloc [Hbind [Hext [Hblocks' Hmemory']]]]]]]].
  assert (Hcoherent' : coherent_layout (extended_parameter_call_layout cells callee data)).
  { eapply allocated_parameter_layout_coherent; eauto. exact (initialized_object_cells _ _ _ _ _ Hmemory). }
  assert (Hcallee : packet_variable_layout (bind_vars globals (fn_args fn)) Sigma' ge callee
    (extended_parameter_call_layout cells callee data) objects packets).
  { eapply function_parameter_packet_callee_bindings; eauto. }
  assert (Hbodytyped : type_expr ge.(genv_cenv) (bind_vars globals (fn_args fn)) Sigma'
    (fn_body fn) (fn_effect fn) (fn_return fn)).
  { eapply (proj2 typing_store_extension); eauto. }
  assert (Hannotations : typeof_exprs es = seq.unzip2 (fn_args fn)) by
    (eapply typed_arguments_annotations; eauto).
  assert (Hpackets' : packet_heap_invariant ge Sigma' initialized objects
    (extended_parameter_call_layout cells callee data) packets).
  { eapply parameter_preparation_packet_heap; eauto. }
  assert (Hextent' : heap_block_extents Sigma' initialized objects
    (extended_parameter_call_layout cells callee data) packets).
  { eapply parameter_preparation_extents; eauto. }
  exists callee, initialized, Sigma', data. split.
  - unfold type_of_function. rewrite <- Hannotations. eapply ssem_app_code_parameters; eauto; reflexivity.
  - split.
    + constructor; try assumption; intros; try assumption. left; assumption.
    + split; [eapply internal_code_contract_store_extension; eauto|]. split.
      2: { exists codes, data_values, allocated. repeat split; assumption. }
      split; [|exact Hcoherent'].
      constructor.
      * constructor; try assumption. eapply packet_variable_layout_extend with (Sigma := Sigma) (cells := cells)
          (objects := objects) (packets := packets);
          [exact Hext|intros; left; assumption|auto|auto|exact Hcaller].
      * eapply ty_callframe; exact Hbodytyped.
      * simpl. eapply runtime_locations_monotone; [|exact Hbodylocations].
        apply packet_heap_locations_monotone; [intros; left; assumption|auto|auto].
      * simpl. exists (bind_vars globals (fn_args fn)), (fn_effect fn).
        split; [exact Hcallee|]. split; [exact Hbodytyped|]. apply frame_free_initialized_frames; exact Hsource.
Qed.

Print Assumptions coherent_function_parameter_entry.

Require Import BeePL_function_parameter_determinism.

Theorem coherent_function_parameter_every_successor :
  forall (ge : genv) Gamma globals Sigma p caller m objects cells packets b fn es argument_effects,
  Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  internal_code_contract ge globals Sigma ->
  has_function_parameter (fn_args fn) ->
  type_exprs ge.(genv_cenv) Gamma Sigma es argument_effects (seq.unzip2 (fn_args fn)) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  all_expr_locations (runtime_locations (packet_heap_locations ge cells objects packets)) es ->
  Forall (fun ty => call_parameter_type ty \/ is_funtype ty = true) (seq.unzip2 (fn_args fn)) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  packet_variable_layout globals Sigma ge empty_vmap cells objects packets ->
  runtime_locations (packet_heap_locations ge cells objects packets) (fn_body fn) ->
  frame_free (fn_body fn) ->
  forall final caller' e',
  ssem_expr ge p caller m
    (App (Val (Vloc b Ptrofs.zero) (type_of_function fn)) es (fn_return fn))
    final caller' e' ->
  exists Sigma' cells',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects cells' packets /\
    internal_code_contract ge globals Sigma' /\
    coherent_runtime_configuration ge Gamma Sigma' caller' final objects cells' packets
      e' (fn_effect fn) (fn_return fn).
Proof.
  intros ge Gamma globals Sigma p caller m objects cells packets b fn es argument_effects
    Hfind Hcode Hhas Harguments Hvalues Hlocations Htypes Hheap Hcoherent
    Hglobals Hbodylocations Hsource final caller' e' Hstep.
  destruct (coherent_function_parameter_entry ge Gamma globals Sigma p caller m objects cells packets
    b fn es argument_effects Hfind Hcode Hhas Harguments Hvalues Hlocations Htypes
    Hheap Hcoherent Hglobals Hbodylocations Hsource)
    as [callee [initialized [Sigma' [data [Hentry [Hevolution [Hcode' [Hconfig
      [codes [data_values [allocated [Hpartition [Hdata [Halloc Hbind]]]]]]]]]]]]]].
  assert (Hnames : NoDup (map fst (fn_args fn))).
  { pose proof (Hcode b fn Hfind) as Hfn. inversion Hfn; subst.
    apply parameter_names_nodup; assumption. }
  destruct (evaluated_code_application_entry_unique ge p caller m b Ptrofs.zero
    (type_of_function fn) es (fn_return fn) fn codes data data_values callee
    Sigma allocated Sigma' initialized ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge cells objects) Hfind Hhas Hvalues Hpartition Hnames
    Hdata Halloc Hbind final caller' e' Hstep) as [Hcaller [Hfinal Hexpr]].
  subst. exists Sigma', (extended_parameter_call_layout cells callee data).
  split; [exact Hevolution|]. split; assumption.
Qed.

Print Assumptions coherent_function_parameter_every_successor.
