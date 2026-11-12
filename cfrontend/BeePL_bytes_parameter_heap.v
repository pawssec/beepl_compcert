(* All scalar array elements, including references and nullable references,
   initialize the same shared heap invariant as aggregate-copy arrays. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory BeePL_scalar_object_layout.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_heap BeePL_packet_coverage.
Require Import BeePL_packet_location_coherence BeePL_packet_mutation BeePL_packet_bindings.
Require Import BeePL_general_array_initialization BeePL_callable_scalar_arrays BeePL_copy_array_heap.
Require Import BeePL_fresh_copy BeePL_initializer_frames BeePL_array_proofs BeePL_heap_extents BeePL_storage_types.
Require Import BeePL_layout_coherence BeePL_initialized_runtime BeePL_initialized_call_entry BeePL_object_separation.
Require Import BeePL_soundness_arrays BeePL_callable_array_objects.
Import ListNotations.
Local Open Scope Z_scope.

Require Import BeePL_structure_proofs BeePL_block_extents BeePL_initializer_slot BeePL_general_parameter_binding.

Require Import BeePL_bytes_execution BeePL_call_bindings BeePL_packet_object_layout.

Theorem initialize_preallocated_bytes_parameter : forall ge Gamma Sigma caller m objects cells packets
    id src source target callee,
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->
  packets src source -> Sigma ! target=Some Bytes ->callee ! id=Some(target,Bytes) ->
  source_block_extent m target packet_descriptor_size ->
  (forall b base root,objects b base root ->b<>target) ->
  (forall b ofs root ch,cells b ofs root ch ->b<>target) ->packet_block_disjoint m packets target ->
  exists final,
    bind_variables ge callee m [(id,Bytes)] [Vloc src source] final /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells
      (extend_packet_locations packets target Ptrofs.zero).
Proof.
  intros ge Gamma Sigma caller m objects cells packets id src source target callee
    Hheap Hsource Hsigma Hget Hextent HobjectsApart HcellsApart HpacketsApart.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  pose proof(packet_heap_valid _ _ _ _ _ _ Hpacket) as Hvalid.
  destruct(Hvalid _ _ Hsource) as [Hbound [view [contents [Hdescriptor Hcontents]]]].
  assert(Hreplacement:packet_descriptor_replacement_separated m packets target Ptrofs.zero).
  { intros b ofs Hin;destruct(HpacketsApart _ _ Hin) as [Hb Hv];split.
    - right;right;left;exact Hb.
    - intros vw Hvw;right;left;apply Hv;exact Hvw. }
  destruct(bytes_descriptor_copy_execution ge m src source target Ptrofs.zero view Hdescriptor Hbound)
    as [final [Hassign Hcopied]].
  - rewrite Ptrofs.unsigned_zero;pose proof(source_extent_bound _ _ _ Hextent);unfold Ptrofs.max_unsigned in H;lia.
  - rewrite Ptrofs.unsigned_zero,Z.add_0_l. intros position Hin;eapply Mem.perm_implies;
      [apply(source_extent_freeable _ _ _ Hextent);exact Hin|constructor].
  - rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r.
  - left;exact(proj1(HpacketsApart _ _ Hsource)).
  - pose proof(bytes_assignment_packet_state_preservation _ _ _ _ _ _ _ _ _ Hvalid Hsource Hreplacement Hassign) as Hvalid'.
    pose proof(bytes_assignment_packet_view_origin _ _ _ _ _ _ _ _ _ Hvalid Hsource Hreplacement Hassign) as Horigins.
    assert(Hmemory':initialized_object_memory ge Sigma final objects cells).
    { constructor.
      - constructor.
        + exact(aggregate_object_typing _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory)).
        + intros b base root Hin. destruct(aggregate_object_readable _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hin)
            as [Hkind [Hsize [Hend [Hblock Hread]]]]. repeat split;try assumption.
          * eapply assignment_preserves_valid_blocks;eauto.
          * intros position Hi;eapply assignment_preserves_permissions;[exact Hassign|apply Hread;exact Hi].
        + exact(aggregate_object_address_bound _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory)).
      - exact(initialized_object_leaves _ _ _ _ _ Hmemory).
      - intros b ofs ty chunk Hin;eapply assignment_typed_cell_frame;
          [exact Hassign|exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)|eapply HcellsApart;exact Hin].
      - intros b ofs ty chunk Hin loaded Hload.
        destruct(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)
          as [Hmode Hvol Haccess [cv [old [HloadOld [Hdecode Htyped]]]]].
        assert(HreadOld:deref_addr ty m b ofs Full old) by(eapply deref_addr_value;eauto).
        assert(HreadFinal:deref_addr ty final b ofs Full old).
        { eapply deref_addr_value;eauto;simpl.
          rewrite(assignment_load_other_block _ _ _ _ _ _ _ _ _ _ _ _ Hassign);[exact HloadOld|eapply HcellsApart;exact Hin]. }
        assert(loaded=old) by(eapply deref_full_deterministic;eauto). subst loaded.
        eapply initialized_object_locations;eauto.
      - exact(initialized_object_scalar_coherence _ _ _ _ _ Hmemory). }
    assert(Hpacket':packet_heap_invariant ge Sigma final objects cells(extend_packet_locations packets target Ptrofs.zero)).
    { constructor.
      - exact Hvalid'.
      - intros b ofs [Hold|[Hb Ho]].
        + eapply packet_heap_typed;eauto.
        + subst;rewrite Ptrofs.unsigned_zero. change(object_type_at ge.(genv_cenv) Sigma target 0(stored_object_type Bytes)).
          apply object_type_root;[exact Hsigma|change(0<=packet_descriptor_size);pose proof packet_descriptor_size_positive;lia].
      - intros b ofs root Hobj delta Hpath;left;eapply packet_heap_coverage;eauto.
      - intros b ofs ty chunk Hcell descriptor offset Hpacket0;split.
        + destruct Hpacket0 as [Hold|[Hb Ho]].
          * exact(proj1(packet_heap_separation _ _ _ _ _ _ Hpacket _ _ _ _ Hcell _ _ Hold)).
          * subst;right;left;intro Heq;symmetry in Heq;eapply HcellsApart;[exact Hcell|exact Heq].
        + intros vw Hvw. destruct(Horigins _ _ _ Hpacket0 Hvw) as [old [oldofs [Hold Hview]]].
          exact(proj2(packet_heap_separation _ _ _ _ _ _ Hpacket _ _ _ _ Hcell _ _ Hold) _ Hview).
      - intros b base root Hobj delta child Hpath descriptor offset Hpacket0;split.
        + destruct Hpacket0 as [Hold|[Hb Ho]].
          * exact(proj1(packet_heap_object_coherence _ _ _ _ _ _ Hpacket _ _ _ Hobj _ _ Hpath _ _ Hold)).
          * subst;left;right;left;intro Heq;symmetry in Heq;eapply HobjectsApart;[exact Hobj|exact Heq].
        + intros vw Hvw. destruct(Horigins _ _ _ Hpacket0 Hvw) as [old [oldofs [Hold Hview]]].
          exact(proj2(packet_heap_object_coherence _ _ _ _ _ _ Hpacket _ _ _ Hobj _ _ Hpath _ _ Hold) _ Hview). }
    assert(Hextents':heap_block_extents Sigma final objects cells(extend_packet_locations packets target Ptrofs.zero)).
    { eapply heap_extents_registry_frame.
      - eapply heap_extents_assignment;[exact Hextents|exact Hassign].
      - intros b [HS|[HC|[HO|[base [Hold|[Hb Ho]]]]]].
        + left;exact HS.
        + right;left;exact HC.
        + right;right;left;exact HO.
        + right;right;right;eauto.
        + subst;left;exists Bytes;split;[exact Hsigma|reflexivity]. }
    exists final;split;[eapply bind_variables_cons;[exact Hget|exact Hassign|constructor]|].
    constructor;try assumption.
    + apply store_context_extends_refl.
    + intros;assumption.
    + intros;assumption.
    + intros b ty Hentry;eapply assignment_preserves_valid_blocks;[exact Hassign|exact(Hblocks b ty Hentry)].
    + intros;left;assumption.
Qed.
