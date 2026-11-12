(* Complete evaluated Ainit head: storage modes choose a proved concrete
   initializer, and the result retains the shared runtime invariant. *)
Require Import List Bool ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations BeePL_aggregate_memory.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_initialized_unit_arrays.
Require Import BeePL_packet_bindings BeePL_packet_state BeePL_packet_heap BeePL_object_coverage.
Require Import BeePL_scalar_array_heap BeePL_copy_array_heap BeePL_storage_types BeePL_layout_coherence.
Require Import BeePL_array_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Theorem initialize_nonunit_array_heap : forall ge p Gamma Sigma vm m objects cells packets arr elem attr values,
  ge.(genv_cenv)=p.(prog_comp_env) -> initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  coherent_layout cells -> elem<>Utype ->
  Forall(fun v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v elem) nil elem /\
    value_locations(packet_heap_locations ge cells objects packets) v elem) values ->
  storage_type_check ge.(genv_cenv)(Atype elem(Z.of_nat(length values)) attr)=true ->
  exists final fresh cells' packets',
    sem_array_init ge Sigma arr(Atype elem(Z.of_nat(length values)) attr) values vm m
      (PTree.set arr(fresh,Atype elem(Z.of_nat(length values)) attr) vm) final
      (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero(Atype elem(Z.of_nat(length values)) attr)) cells' packets' /\
    coherent_layout cells'.
Proof.
  intros ge p Gamma Sigma vm m objects cells packets arr elem attr values Henv Hheap Hcoherent Hnonunit Hvalues Hstorage.
  destruct elem as [|pt|ptr|sid sa|element count aa|args effects result variadic|];[contradiction| | | | | |].
  - destruct(initialize_scalar_array_heap ge p Gamma Sigma vm m objects cells packets arr(Vtype pt) attr values(chunk_of_ptype pt)
      Henv Hheap Hcoherent Hvalues(primitive_chunk_access pt) Hstorage) as [final [fresh [after [Hinit [Hevolve Hafter]]]]].
    exists final,fresh,after,packets;auto.
  - assert(Hmode:access_mode_type(Ptrtype ptr)=By_value(transl_bchunk_cchunk(if Archi.ptr64 then BMint64 else BMint32))).
    { simpl;unfold Mptr;destruct Archi.ptr64;reflexivity. }
    destruct(initialize_scalar_array_heap ge p Gamma Sigma vm m objects cells packets arr(Ptrtype ptr) attr values
      (if Archi.ptr64 then BMint64 else BMint32) Henv Hheap Hcoherent Hvalues Hmode Hstorage)
      as [final [fresh [after [Hinit [Hevolve Hafter]]]]].
    exists final,fresh,after,packets;auto.
  - eapply initialize_copy_array_heap;eauto;left;reflexivity.
  - eapply initialize_copy_array_heap;eauto;left;reflexivity.
  - rewrite storage_type_function_array_rejected in Hstorage;discriminate.
  - eapply initialize_copy_array_heap;eauto;right;reflexivity.
Qed.

Lemma array_heap_result_configuration : forall ge p Gamma Sigma vm m objects cells packets arr elem attr es values final fresh after finalPackets,
  initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  Forall(fun e=>exists v t,e=Val v t) es -> values=extract_values_exprs es ->
  sem_array_init ge Sigma arr(Atype elem(Z.of_nat(length values)) attr) values vm m
    (PTree.set arr(fresh,Atype elem(Z.of_nat(length values)) attr) vm) final
    (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) ->
  initialized_heap_evolution ge Sigma objects cells packets
    (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Atype elem(Z.of_nat(length values)) attr)) after finalPackets ->
  coherent_layout after ->
  ssem_expr ge p vm m(Ainit arr(Atype elem(Z.of_nat(length values)) attr) es(Atype elem(Z.of_nat(length values)) attr)) final vm
    (Val(Vloc fresh Ptrofs.zero)(Atype elem(Z.of_nat(length values)) attr)) /\
  coherent_runtime_configuration ge Gamma(PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) vm final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Atype elem(Z.of_nat(length values)) attr)) after finalPackets
    (Val(Vloc fresh Ptrofs.zero)(Atype elem(Z.of_nat(length values)) attr)) nil(Atype elem(Z.of_nat(length values)) attr).
Proof.
  intros ge p Gamma Sigma vm m objects cells packets arr elem attr es values final fresh after finalPackets
    Hheap Hvalues Hextracted Hinit Hevolve Hcoherent.
  split.
  - eapply ssem_array_init3;[exact Hvalues|rewrite <-Hextracted;exact Hinit|apply PTree.gss].
  - split;[|exact Hcoherent]. constructor.
    + eapply initialized_heap_state_evolve;eauto.
    + apply ty_valarray. eapply aggregate_object_typing.
      * exact(initialized_object_descriptors _ _ _ _ _(initialized_evolution_memory _ _ _ _ _ _ _ _ _ _ Hevolve)).
      * right;auto.
    + left;apply aggregate_descriptor_direct;[reflexivity|right;auto].
    + exact I.
Qed.

Require Import BeePL_type_equality BeePL_structure_proofs.

Lemma typed_located_equal_array_values : forall env Gamma Sigma es ef ts,
  type_exprs env Gamma Sigma es ef ts -> forall L elem,
  Forall(fun e=>exists v t,e=Val v t) es ->
  all_expr_locations(runtime_locations L) es -> all_eq_type elem ts=true ->
  Forall(fun v=>type_expr env Gamma Sigma(Val v elem) nil elem /\ value_locations L v elem)(extract_values_exprs es).
Proof.
  intros env Gamma Sigma es ef ts Htyped;induction Htyped as [env Gamma Sigma|
    env Gamma Sigma e es ef efs t ts HheadTyped HtailTyped IH];intros L elem Hvalues Hlocations Hequal.
  - constructor.
  - inversion Hvalues as [|first rest Hhead Htail];subst first rest.
    destruct Hhead as [v [annotation He]];subst e.
    simpl in Hequal. apply andb_true_iff in Hequal as [Htype Htypes].
    change(eq_type elem t=true) in Htype;apply eq_type_sound in Htype;subst t.
    assert(Hannotation:annotation=elem) by(eapply typed_value_annotation;eauto).
    assert(Heffect:ef=nil) by(inversion HheadTyped;reflexivity).
    subst annotation ef. simpl in Hlocations;destruct Hlocations as [Hloc Hlocs].
    simpl;constructor;[split;assumption|eapply IH;eauto].
Qed.

Theorem typed_evaluated_array_inputs : forall env Gamma Sigma L arr elem len attr es ef,
  type_expr env Gamma Sigma(Ainit arr(Atype elem len attr) es(Atype elem len attr)) ef(Atype elem len attr) ->
  Forall(fun e=>exists v t,e=Val v t) es ->
  runtime_locations L(Ainit arr(Atype elem len attr) es(Atype elem len attr)) ->
  ef=nil /\ len=Z.of_nat(length(extract_values_exprs es)) /\
  Forall(fun v=>type_expr env Gamma Sigma(Val v elem) nil elem /\ value_locations L v elem)(extract_values_exprs es) /\
  storage_type_check env(Atype elem len attr)=true.
Proof.
  intros env Gamma Sigma L arr elem len attr es ef Htyped Hvalues Hlocations.
  pose proof(typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped) as [_ [element [a Hextent]]].
  inversion Hextent.
  assert(Hlength:len=Z.of_nat(length(extract_values_exprs es))).
  { rewrite extracted_value_arguments_length by exact Hvalues;congruence. }
  inversion Htyped;subst.
  match goal with Hget:get_array_elm_ty _=OK _|-_=>simpl in Hget;inversion Hget;subst end.
  split;[eapply value_arguments_effect_nil;eauto|]. split;[exact Hlength|]. split.
  - eapply typed_located_equal_array_values;eauto.
  - assumption.
Qed.

Theorem coherent_general_array_progress : forall ge p Gamma Sigma vm m objects cells packets arr elem len attr es ef,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr(Atype elem len attr) es(Atype elem len attr)) ef(Atype elem len attr) ->
  Forall(fun e=>exists v t,e=Val v t) es ->
  exists final fresh Sigma' objects' cells' packets',
    ssem_expr ge p vm m(Ainit arr(Atype elem len attr) es(Atype elem len attr)) final vm
      (Val(Vloc fresh Ptrofs.zero)(Atype elem len attr)) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm final objects' cells' packets'
      (Val(Vloc fresh Ptrofs.zero)(Atype elem len attr)) ef(Atype elem len attr).
Proof.
  intros ge p Gamma Sigma vm m objects cells packets arr elem len attr es ef Henv Hconfig Hvalues.
  destruct(eq_type elem Utype) eqn:Hunit.
  - apply eq_type_sound in Hunit;subst elem.
    destruct(coherent_unit_array_progress ge Gamma Sigma objects cells packets p vm m arr len attr es ef Hconfig Hvalues)
      as [final [fresh [Sigma' [objects' [Hstep [Hevolve Hfinal]]]]]].
    exists final,fresh,Sigma',objects',cells,packets;auto.
  - assert(Hnonunit:elem<>Utype) by(intro Heq;subst elem;discriminate Hunit).
    destruct Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
    destruct(typed_evaluated_array_inputs _ _ _ _ _ _ _ _ _ _ Htyped Hvalues Hlocations)
      as [Hef [Hlen [HtypedValues Hstorage]]]. subst ef len.
    destruct(initialize_nonunit_array_heap ge p Gamma Sigma vm m objects cells packets arr elem attr(extract_values_exprs es)
      Henv Hheap Hcoherent Hnonunit HtypedValues Hstorage)
      as [final [fresh [after [finalPackets [Hinit [Hevolve Hafter]]]]]].
    destruct(array_heap_result_configuration ge p Gamma Sigma vm m objects cells packets arr elem attr es (extract_values_exprs es) final fresh after finalPackets Hheap Hvalues eq_refl Hinit Hevolve Hafter)
      as [Hstep Hfinal].
    exists final,fresh,(PTree.set fresh(Atype elem(Z.of_nat(length(extract_values_exprs es))) attr) Sigma),
      (add_aggregate_descriptor objects fresh Ptrofs.zero(Atype elem(Z.of_nat(length(extract_values_exprs es))) attr)),after,finalPackets.
    split;[exact Hstep|]. split;assumption.
Qed.

Require Import BeePL_initializer_determinism.

Theorem coherent_general_array_preservation : forall ge p Gamma Sigma vm m objects cells packets arr elem len attr es ef final vm' e',
  ge.(genv_cenv)=p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr(Atype elem len attr) es(Atype elem len attr)) ef(Atype elem len attr) ->
  Forall(fun e=>exists v t,e=Val v t) es ->
  ssem_expr ge p vm m(Ainit arr(Atype elem len attr) es(Atype elem len attr)) final vm' e' ->
  exists Sigma' objects' cells' packets',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' e' ef(Atype elem len attr).
Proof.
  intros ge p Gamma Sigma vm m objects cells packets arr elem len attr es ef final vm' e'
    Henv Hconfig Hvalues Hstep.
  destruct(coherent_general_array_progress ge p Gamma Sigma vm m objects cells packets arr elem len attr es ef Henv Hconfig Hvalues)
    as [chosen [fresh [Sigma' [objects' [cells' [packets' [Hchosen [Hevolve Hfinal]]]]]]]].
  destruct(evaluated_array_step_unique ge p vm m arr(Atype elem len attr) es chosen vm
    (Val(Vloc fresh Ptrofs.zero)(Atype elem len attr)) final vm' e' Hvalues Hchosen Hstep)
    as [Hmem [Hvm He]]. subst final vm' e'.
  exists Sigma',objects',cells',packets';split;assumption.
Qed.

Print Assumptions typed_evaluated_array_inputs.
Print Assumptions coherent_general_array_progress.
Print Assumptions coherent_general_array_preservation.
