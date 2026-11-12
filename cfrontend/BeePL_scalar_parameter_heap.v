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

Theorem initialize_preallocated_scalar_parameter : forall ge Gamma Sigma caller m objects cells packets
    id ty v target callee chunk,
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  access_mode_type ty=By_value(transl_bchunk_cchunk chunk) -> storage_type_check ge.(genv_cenv) ty=true ->
  type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty ->
  value_locations(packet_heap_locations ge cells objects packets) v ty ->
  Sigma ! target=Some ty -> callee ! id=Some(target,ty) ->
  source_block_extent m target(sizeof_type ge.(genv_cenv) ty) ->
  (forall b base root,objects b base root ->b<>target) ->
  (forall b ofs root ch,cells b ofs root ch ->b<>target) ->packet_block_disjoint m packets target ->
  exists final,
    bind_variables ge callee m [(id,ty)] [v] final /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects
      (extend_scalar_layout cells target Ptrofs.zero ty chunk) packets /\
    coherent_layout(extend_scalar_layout cells target Ptrofs.zero ty chunk).
Proof.
  intros ge Gamma Sigma caller m objects cells packets id ty v target callee chunk
    Hheap Hcoherent Hmode Hstorage Htyped Hloc Hsigma Hget Hextent HobjectsApart HcellsApart HpacketsApart.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  assert(Hloc':value_locations(descriptor_heap_locations ge cells objects) v ty).
  { eapply packet_value_locations_nonbytes;[intro Heq;subst ty;discriminate Hmode|exact Hloc]. }
  assert(Haccess:Mem.valid_access m(transl_bchunk_cchunk chunk) target(Ptrofs.unsigned Ptrofs.zero) Freeable).
  { split;[|rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r]. rewrite Ptrofs.unsigned_zero,Z.add_0_l.
    rewrite(scalar_type_chunk_size ge.(genv_cenv) _ _ Hmode);exact(source_extent_freeable _ _ _ Hextent). }
  destruct(initialize_typed_scalar_array_cell ge ge.(genv_cenv) Gamma Sigma(descriptor_heap_locations ge cells objects)
    m target Ptrofs.zero ty chunk v Htyped Hloc' Hmode(storage_type_nonvolatile _ _ Hstorage) Haccess)
    as [final [Hstore [Hassign [Hcell HcellLoc]]]].
  assert(Hapart:slot_cells_disjoint cells target(Ptrofs.unsigned Ptrofs.zero)(size_chunk(transl_bchunk_cchunk chunk))).
  { intros;left;eapply HcellsApart;eauto. }
  destruct(scalar_slot_memory_frame _ _ _ _ _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory)(initialized_object_locations _ _ _ _ _ Hmemory)
    Hapart Hstore Hcell HcellLoc) as [Hcells' Hlocations'].
  pose proof(packet_heap_valid _ _ _ _ _ _ Hpacket) as Hvalid.
  destruct(packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hvalid HpacketsApart Hassign) as [Hvalid' Hviews].
  assert(Hpacket':packet_heap_invariant ge Sigma final objects
    (extend_scalar_layout cells target Ptrofs.zero ty chunk) packets).
  { constructor.
    - exact Hvalid'.
    - exact(packet_heap_typed _ _ _ _ _ _ Hpacket).
    - exact(packet_heap_coverage _ _ _ _ _ _ Hpacket).
    - intros b ofs root ch [Hold|[Hb [Hofs [Hty Hchunk]]]].
      + eapply packet_layout_separation_frame;[exact Hvalid|exact Hviews| |exact Hold].
        exact(packet_heap_separation _ _ _ _ _ _ Hpacket).
      + subst;eapply packet_block_disjoint_write.
        eapply packet_block_disjoint_frame;[exact Hvalid|exact Hviews|exact HpacketsApart].
    - eapply packet_object_coherence_frames;[exact Hvalid|exact Hviews|].
      exact(packet_heap_object_coherence _ _ _ _ _ _ Hpacket). }
  assert(Hmemory':initialized_object_memory ge Sigma final objects
    (extend_scalar_layout cells target Ptrofs.zero ty chunk)).
  { constructor.
    - constructor.
      + exact(aggregate_object_typing _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory)).
      + intros b base root Hin. destruct(aggregate_object_readable _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hin)
          as [Hkind [Hsize [Hbound [Hblock Hread]]]].
        repeat split;try assumption.
        * eapply assignment_preserves_valid_blocks;eauto.
        * intros position Hi;eapply assignment_preserves_permissions;[exact Hassign|apply Hread;exact Hi].
      + exact(aggregate_object_address_bound _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory)).
    - intros b base root Hin delta t ch Hleaf.
      destruct(initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hin _ _ _ Hleaf) as [stored [Hbefore Heq]].
      exists stored;split;[left;exact Hbefore|exact Heq].
    - exact Hcells'.
    - intros b ofs root ch Hin loaded Hread;eapply value_locations_monotone;[|eapply Hlocations';eauto].
      apply descriptor_heap_locations_monotone;[intros;left;assumption|intros;assumption].
    - intros b base root Hin delta child Hpath other offset t ch [Hold|[Hb Hrest]].
      + eapply initialized_object_scalar_coherence;eauto.
      + left;left;subst other;intro Heq;symmetry in Heq;eapply HobjectsApart;eauto. }
  assert(Hextents':heap_block_extents Sigma final objects
    (extend_scalar_layout cells target Ptrofs.zero ty chunk) packets).
  { eapply heap_extents_registry_frame.
    - eapply heap_extents_assignment;[exact Hextents|exact Hassign].
    - intros b [HS|[[ofs [root [ch [Hold|[Hb Hrest]]]]]|Hrest]].
      + left;exact HS.
      + right;left;eauto.
      + subst;left;exists ty;split;[exact Hsigma|destruct ty;try reflexivity;discriminate Hmode].
      + right;right;exact Hrest. }
  exists final;split;[eapply bind_variables_cons;[exact Hget|exact Hassign|constructor]|]. split.
  - constructor;try assumption.
    + apply store_context_extends_refl.
    + intros;left;assumption.
    + intros;assumption.
    + intros b root Hentry;eapply assignment_preserves_valid_blocks;[exact Hassign|eapply Hblocks;exact Hentry].
    + intros;assumption.
  - eapply scalar_slot_extension_coherent;[exact Hcoherent|exact Hapart].
Qed.
