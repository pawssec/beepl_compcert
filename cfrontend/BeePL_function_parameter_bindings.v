(* Callee lookup maps combine immutable authentic code aliases with newly
   allocated data slots; globally scoped code is used only when unshadowed. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_soundness_variables.
Require Import BeePL_callable_locations BeePL_callable_variables BeePL_call_state.
Require Import BeePL_parameter_allocations BeePL_scalar_parameters BeePL_call_parameters.
Require Import BeePL_call_parameter_layout BeePL_function_parameters.
Require Import BeePL_scalar_call_layout BeePL_allocation_proofs.
Import ListNotations.

Theorem function_parameter_callee_bindings :
  forall ge Sigma Sigma' globals cells params values codes data data_values m callee allocated,
  function_parameter_partition ge params values codes data data_values ->
  NoDup (map fst params) ->
  Forall (fun param => call_parameter_type (snd param)) data ->
  callable_variable_layout globals Sigma ge empty_vmap cells ->
  alloc_variables ge Sigma codes m data callee allocated Sigma' ->
  store_context_extends Sigma Sigma' ->
  callable_variable_layout (bind_vars globals params) Sigma' ge callee
    (extended_parameter_call_layout cells callee data).
Proof.
  intros ge Sigma Sigma' globals cells params values codes data data_values m callee allocated
    Hpartition Hnames Htypes Hglobals Halloc Hext x ty Hlookup.
  destruct (bind_vars_lookup_origin _ _ _ _ Hlookup) as [Hin|[Hglobal Hmissing]].
  - destruct (function_partition_parameter_origin _ _ _ _ _ _ Hpartition Hnames x ty Hin)
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
    destruct (Hglobals x ty Hglobal) as [b Hlocation Hbinding Hnonfun|b Hnone Hsymbol Hcode|b Hlocal Hcode].
    + eapply callable_variable_data with (b := b); [| |exact Hnonfun].
      * destruct Hlocation as [Hlocal|[Hnone Hsymbol]].
        -- unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
        -- right; split; assumption.
      * eapply heap_variable_binding_extend; [exact Hext| |exact Hbinding].
        intros block ofs t chunk Hentry. left; exact Hentry.
    + eapply callable_variable_code; eauto.
    + unfold empty_vmap in Hlocal. rewrite PTree.gempty in Hlocal. discriminate.
Qed.

Print Assumptions function_parameter_callee_bindings.
