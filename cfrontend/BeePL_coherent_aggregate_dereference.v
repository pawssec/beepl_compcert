(* Aggregate references point at registered initialized objects. Dereferencing
   exposes that existing object and leaves memory and the shared heap unchanged. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations BeePL_soundness_arrays.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_aggregate_dereference.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_initialized_runtime.
Require Import BeePL_coherent_configurations.
Import ListNotations.

Lemma coherent_aggregate_reference_object :
  forall ge Sigma m objects cells packets b base basic attr,
  initialized_object_memory ge Sigma m objects cells ->
  is_aggregate_type (construct_type_btype basic) = true ->
  packet_heap_locations ge cells objects packets b base (Ptrtype (Reftype basic attr)) ->
  objects b base (construct_type_btype basic).
Proof.
  intros * Hmemory Hkind Hlocation.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  destruct Hlocation as [Hcall | [[Hbad Hobject] | [other [pa [Heq [Haggregate Hobject]]]]]].
  - destruct Hcall as [[pt [chunk [Heq Hcell]]] | [elem [len [a [Heq Hrest]]]]];
      [|discriminate Heq].
    inversion Heq; subst pt.
    pose proof (typed_cell_access _ _ _ _ _ _ _
      (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
    destruct basic; simpl in Hkind; try discriminate; discriminate Hmode.
  - discriminate Hbad.
  - inversion Heq; subst. exact Hobject.
Qed.

Theorem coherent_aggregate_deref_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base basic attr ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic)) ef (construct_type_btype basic) ->
  is_aggregate_type (construct_type_btype basic) = true ->
  ssem_expr ge p vm m
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic)) m vm (Val (Vloc b base) (construct_type_btype basic)) /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Val (Vloc b base) (construct_type_btype basic)) nil (construct_type_btype basic).
Proof.
  intros * Hconfig Hkind.
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
  pose proof (initialized_heap_memory _ _ _ _ _ _ _ _ Hheap) as Hmemory.
  assert (Hobject : objects b base (construct_type_btype basic)).
  { eapply coherent_aggregate_reference_object; [exact Hmemory |exact Hkind |exact (proj1 Hlocations)]. }
  destruct (aggregate_descriptor_dereference_progress ge Gamma Sigma p vm m cells objects b base basic attr
    (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject) as [Hstep [Hvalue Hlocated]].
  split; [exact Hstep |]. split.
  - eapply initialized_heap_evolution_refl; exact Hheap.
  - split; [|exact Hcoherent]. constructor; [exact Hheap |exact Hvalue | |exact I].
    left; exact Hlocated.
Qed.

Theorem coherent_aggregate_deref_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base basic attr ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic)) ef (construct_type_btype basic) ->
  is_aggregate_type (construct_type_btype basic) = true ->
  ssem_expr ge p vm m
    (Prim Deref [Val (Vloc b base) (Ptrtype (Reftype basic attr))]
      (construct_type_btype basic)) final vm' next ->
  final = m /\ vm' = vm /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets
    next nil (construct_type_btype basic).
Proof.
  intros * Hconfig Hkind Hstep.
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
  pose proof (initialized_heap_memory _ _ _ _ _ _ _ _ Hheap) as Hmemory.
  assert (Hobject : objects b base (construct_type_btype basic)).
  { eapply coherent_aggregate_reference_object; [exact Hmemory |exact Hkind |exact (proj1 Hlocations)]. }
  destruct (aggregate_descriptor_dereference_preservation ge Gamma Sigma p vm m cells objects b base basic attr
    final vm' next (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject Hstep)
    as [Hm [Hvm [He [Hvalue Hlocated]]]].
  subst final vm' next.
  destruct (coherent_aggregate_deref_progress ge Gamma Sigma vm m objects cells packets p b base basic attr ef
    Hconfig Hkind) as [_ [Hevolve Hfinal]].
  split; [reflexivity |]. split; [reflexivity |]. split; assumption.
Qed.

Print Assumptions coherent_aggregate_deref_progress.
Print Assumptions coherent_aggregate_deref_preservation.
