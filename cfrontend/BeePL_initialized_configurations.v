Require Import BeePL_heap_extents BeePL_block_extents BeePL_storage_types.
(* Actual initializer and variable steps in the shared initialized-object
   configuration. These are cases for the whole-language induction. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations BeePL_array_proofs.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_initialized_arrays.
Require Import BeePL_callable_variables BeePL_initialized_variables BeePL_initialized_runtime.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_initializer_frames BeePL_fresh_copy.
Import ListNotations.
Local Open Scope Z_scope.


Lemma completed_array_extents : forall ge Sigma m objects cells packets p vm arr elem len attr es
    final vm' fresh cells',
  heap_block_extents Sigma m objects cells packets ->
  0 <= sizeof_type ge.(genv_cenv) (Atype elem len attr) <= Ptrofs.max_unsigned ->
  (forall b ofs ty chunk, cells' b ofs ty chunk -> cells b ofs ty chunk \/ b=fresh) ->
  ssem_expr ge p vm m (Ainit arr (Atype elem len attr) es (Atype elem len attr))
    final vm' (Val (Vloc fresh Ptrofs.zero) (Atype elem len attr)) ->
  heap_block_extents (PTree.set fresh (Atype elem len attr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype elem len attr)) cells' packets.
Proof.
  intros * Hextents Hsize Hcells Hstep. inversion Hstep; subst.
  match goal with Hi : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hi)
      as [allocated [actual [Ha [Hlookup [Hhelper Hrest]]]]]
  end.
  assert (actual=fresh) by congruence. subst actual.
  eapply heap_extents_array_helper; [|exact Hhelper].
  eapply heap_extents_allocation; [exact Hextents|exact Ha|exact Hsize|].
  eapply tracked_data_block_same_block_extension.
  - intros; eapply store_set_lookup_origin; eauto.
  - intros b base ty [Hold|[Hb HobjectRest]]; [left; exact Hold|right; exact Hb].
  - exact Hcells.
  - intros; left; assumption.
Qed.

Lemma completed_primitive_array_packets : forall ge Sigma larger m objects cells packets p vm arr pt len attr es final vm' fresh,
  packet_heap_invariant ge Sigma m objects cells packets ->
  store_context_extends Sigma larger ->
  ssem_expr ge p vm m (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr))
    final vm' (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ->
  packet_heap_invariant ge larger final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
    (extend_array_layout cells fresh pt (length es)) packets.
Proof.
  intros * Hp Hext Hstep. inversion Hstep; subst.
  match goal with Hi : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hi)
      as [allocated [actual [Ha [Hlookup [Hhelper Hrest]]]]]
  end.
  assert (actual=fresh) by congruence. subst actual.
  eapply packet_heap_fresh_array_elements; eauto.
  - apply primitive_array_has_no_bytes_leaf.
  - intros b ofs ty chunk [Hold|[index [Hindex [Hb Hother]]]]; eauto.
Qed.

Theorem initialized_array_configuration_preservation :
  forall ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm' e' ->
  exists Sigma' objects' cells',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets /\
    initialized_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets e' ef
      (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef final vm' e'
    [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes] Hvalues Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]].
  - subst final vm' e'. exists Sigma, objects, cells. split.
    + constructor; auto; try apply store_context_extends_refl.
    + constructor; [constructor; assumption|assumption|assumption|assumption].
  - subst e'.
    destruct (completed_initialized_array_preservation ge Gamma Sigma objects cells p vm m arr pt len attr
      es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep)
      as [Sigma' [HSigma [Hvm [Hext [Hblocks' [Hmemory' Htyped']]]]]].
    assert (Hpacket' : packet_heap_invariant ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) packets).
    { eapply completed_primitive_array_packets; eauto. }
    assert (Hextents' : heap_block_extents Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) packets).
    { rewrite HSigma. eapply completed_array_extents; [exact Hextents| | |exact Hstep].
      - eapply storage_type_size_bounds. inversion Htyped; subst; assumption.
      - intros b ofs ty chunk [Hold|[i [Hi [Hb Hrest]]]]; [left; exact Hold|right; exact Hb]. }
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr)),
      (extend_array_layout cells fresh pt (length es)).
    split.
    + constructor; try assumption; intros; try (left; assumption); assumption.
    + constructor.
      * constructor; try assumption. subst vm'. eapply packet_variable_layout_extend with (cells := cells) (objects := objects) (packets := packets);
          [exact Hext|intros; left; assumption|intros; left; assumption|intros; assumption|exact Hbindings].
      * exact Htyped'.
      * left; apply aggregate_descriptor_direct; [reflexivity|right; auto].
      * exact I.
Qed.

Theorem initialized_array_configuration_progress :
  forall ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  exists final fresh Sigma' objects' cells',
    ssem_expr ge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets /\
    initialized_runtime_configuration ge Gamma Sigma' vm final objects' cells' packets
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef Hconfig Hvalues.
  destruct Hconfig as [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes].
  destruct (initialized_array_progress ge Gamma Sigma objects cells p vm m arr pt len attr es ef
    Htyped Hvalues Hblocks Hmemory)
    as [final [fresh [allocated [Hstep Hrest]]]].
  assert (Hconfig : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr)).
  { constructor; [constructor; assumption |assumption |assumption |assumption]. }
  destruct (initialized_array_configuration_preservation ge Gamma Sigma objects cells packets p vm m arr pt len attr
    es ef final vm _ Hconfig Hvalues Hstep)
    as [Sigma' [objects' [cells' [Hevolve Hfinal]]]].
  exists final, fresh, Sigma', objects', cells'. split; [exact Hstep |]. split; assumption.
Qed.

Theorem initialized_variable_configuration_progress :
  forall ge Gamma Sigma vm m objects cells packets p x ty ef,
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Var x ty) ef ty ->
  exists v,
    ssem_expr ge p vm m (Var x ty) m vm (Val v ty) /\
    initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v ty) ef ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p x ty ef
    [Hheap Htyped Hlocations Hframes].
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents]. inversion Htyped; subst.
  destruct (packet_variable_progress Gamma Sigma ge vm cells objects packets p m x ty
    Hbindings (initialized_object_cells _ _ _ _ _ Hmemory)
    ltac:(intros b ofs t chunk Hcell v Hread; eapply value_locations_monotone; [apply packet_descriptor_embedding|eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto])
    (initialized_object_descriptors _ _ _ _ _ Hmemory)
    (packet_heap_valid _ _ _ _ _ _ Hpacket) (packet_heap_typed _ _ _ _ _ _ Hpacket) ltac:(assumption)) as [v [Hstep [Hvalue Hloc]]].
  exists v. split; [exact Hstep |]. constructor.
  - constructor; assumption.
  - exact Hvalue.
  - exact Hloc.
  - exact I.
Qed.

Theorem initialized_variable_configuration_preservation :
  forall ge Gamma Sigma vm m objects cells packets p x ty ef final vm' e',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Var x ty) ef ty ->
  ssem_expr ge p vm m (Var x ty) final vm' e' ->
  initialized_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' ef ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p x ty ef final vm' e'
    [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes] Hstep.
  inversion Htyped; subst.
  destruct (packet_variable_preservation Gamma Sigma ge vm cells objects packets p m x ty final vm' e'
    Hbindings (initialized_object_cells _ _ _ _ _ Hmemory)
    ltac:(intros b ofs t chunk Hcell v Hread; eapply value_locations_monotone; [apply packet_descriptor_embedding|eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto])
    (initialized_object_descriptors _ _ _ _ _ Hmemory)
    (packet_heap_valid _ _ _ _ _ _ Hpacket) (packet_heap_typed _ _ _ _ _ _ Hpacket)
    ltac:(assumption) Hstep) as [Hm [Hvm [Hvalue Hloc]]].
  subst final vm'. constructor.
  - constructor; assumption.
  - exact Hvalue.
  - exact Hloc.
  - inversion Hstep; subst; exact I.
Qed.

Print Assumptions initialized_array_configuration_preservation.
Print Assumptions initialized_array_configuration_progress.
Print Assumptions initialized_variable_configuration_progress.
Print Assumptions initialized_variable_configuration_preservation.
