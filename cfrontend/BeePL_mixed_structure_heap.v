(* Complete heterogeneous field initialization registers the finished parent
   only after deriving coverage for all declared scalar and packet leaves. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_structure_field_planning BeePL_mixed_structure_fields BeePL_mixed_structure_coverage.
Require Import BeePL_structure_storage_typing BeePL_structure_proofs BeePL_initialized_structures.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory BeePL_scalar_object_layout.
Require Import BeePL_callable_array_objects BeePL_initializer_coherence BeePL_object_separation.
Require Import BeePL_packet_heap BeePL_packet_state BeePL_packet_mutation BeePL_packet_bindings BeePL_packet_coverage BeePL_packet_object_layout.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_copy BeePL_parameter_packet_assembly.
Require Import BeePL_storage_types BeePL_heap_extents BeePL_block_extents.
Require Import BeePL_fresh_copy BeePL_initializer_frames BeePL_layout_coherence BeePL_initialized_runtime.
Require Import BeePL_copy_array_heap BeePL_coherent_fields BeePL_initialized_call_entry.
Require Import BeePL_array_copy_sources BeePL_general_array_initialization.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mixed_sources_allocation_frame : forall env seed packets m allocated dst lo hi fresh fields,
 mixed_field_sources env seed packets m dst fields ->Mem.alloc m lo hi=(allocated,fresh) ->
 mixed_field_sources env seed packets allocated dst fields.
Proof.
 intros * Hsources Halloc;eapply Forall_impl;[|exact Hsources]. intros field Hsource Hkind.
 destruct(Hsource Hkind) as [src base Hv Hneq Hvalid Hbound Halign Hread Hcoverage Hregions Hpackets].
 eapply array_copy_source_intro with(src:=src)(source:=base);try assumption.
 - eapply Mem.valid_block_alloc;eauto.
 - intros ofs Hin;eapply Mem.perm_alloc_1;[exact Halloc|apply Hread;exact Hin].
Qed.

Lemma typed_mixed_structure_names : forall env Gamma Sigma sid co fields result ef,
 type_expr env Gamma Sigma(Sinit sid(map field_slot_name fields)(map field_slot_expression fields) result) ef result ->
 PTree.get sid env=Some co ->map field_slot_name fields=map Ctypes.name_member
 (bmembers_cmembers(filter(fun member=>negb(member_is_padding member)) co.(co_members))).
Proof. intros * Htyped Hco;inversion Htyped;subst;assert(co0=co) by congruence;subst co0;assumption. Qed.

Theorem initialize_mixed_structure_heap : forall p Gamma Sigma vm m objects cells packets sid attr pa co fields result ef,
 initialized_heap_state(globalenv p) Gamma Sigma vm m objects cells packets ->coherent_layout cells ->
 type_expr p.(prog_comp_env) Gamma Sigma(Sinit sid(map field_slot_name fields)(map field_slot_expression fields) result) ef result ->
 structure_result_type sid attr result ->PTree.get sid p.(prog_comp_env)=Some co ->
 Forall(evaluated_field_valid p Gamma Sigma(packet_heap_locations(globalenv p) cells objects packets) sid attr co) fields ->
 exists allocated final fresh after,
 Mem.alloc m 0(sizeof_type p.(prog_comp_env)(Stype sid attr))=(allocated,fresh) /\
 sem_allocate_fields(globalenv p) fresh Ptrofs.zero sid(map field_slot_name fields)
 (map field_slot_value fields)(map field_slot_type fields) allocated final /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets
 (PTree.set fresh(Ptrtype(Reftype(Bstruct sid attr)pa)) Sigma) final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after
 (copied_object_packets p.(prog_comp_env) packets(Stype sid attr) fresh) /\coherent_layout after.
Proof.
 intros * Hheap Hcoherent Htyped Hshape Hco Hfields.
 destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
 pose proof(typed_structure_storage_admissible _ _ _ _ _ _ _ _ _ Htyped Hshape) as Hstorage.
 pose proof(storage_type_size_bounds _ _ Hstorage) as Hsize.
 destruct(Mem.alloc m 0(sizeof_type p.(prog_comp_env)(Stype sid attr))) as [allocated fresh] eqn:Halloc.
 pose proof(Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hfresh.
 assert(HcellsAllocated:typed_memory_layout p.(prog_comp_env) Sigma cells allocated).
 { intros b ofs ty ch Hin;eapply typed_memory_cell_alloc_frame;
 [exact Halloc|exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)]. }
 assert(HlocationsAllocated:memory_locations(packet_heap_locations(globalenv p) cells objects packets) cells allocated).
 { intros b ofs ty ch Hin value Hread;eapply value_locations_monotone;[apply packet_descriptor_embedding|].
   eapply allocation_memory_locations;[exact(initialized_object_cells _ _ _ _ _ Hmemory)|
   exact(initialized_object_locations _ _ _ _ _ Hmemory)|exact Halloc|exact Hin|exact Hread]. }
 assert(Hsources:mixed_field_sources p.(prog_comp_env) cells packets m fresh fields).
 { apply Forall_forall;intros field Hin Hkind.
   pose proof(proj1(Forall_forall _ _) Hfields field Hin) as [Ht [Hl Hrest]].
   eapply (typed_located_array_copy_source (globalenv p) p);[reflexivity|exact Hmemory|exact Hcoherent|exact Hpacket|exact Hextents|exact Ht|exact Hl|exact Hkind|exact Hfresh]. }
 pose proof(mixed_sources_allocation_frame _ _ _ _ _ _ _ _ _ _ Hsources Halloc) as HsourcesAllocated.
 assert(HcellApart:forall b ofs ty ch,cells b ofs ty ch ->b<>fresh).
 { intros b ofs ty ch Hin Heq;subst b;apply Hfresh;eapply initialized_scalar_valid_block;
 eapply typed_memory_cell_erasure;exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin). }
 assert(Hregion:scalar_object_region_coherent p.(prog_comp_env) cells fresh 0(Stype sid attr)).
 { intros b ofs ty ch Hin;left;left;eapply HcellApart;exact Hin. }
 pose proof(allocated_packet_block_disjoint _ _ _ _ _ _(packet_heap_valid _ _ _ _ _ _ Hpacket) Halloc) as HpacketApartAllocated.
 assert(HpacketRegion:packet_object_region_coherent p.(prog_comp_env) allocated packets fresh 0(Stype sid attr)).
 { intros b ofs Hin;split;[left;right;left;exact(proj1(HpacketApartAllocated _ _ Hin))|].
 intros view Hview;right;left;exact(proj2(HpacketApartAllocated _ _ Hin) view Hview). }
 destruct(initialize_mixed_structure_fields fields p Gamma Sigma _ sid attr co cells packets cells packets allocated fresh
 Hco Hstorage Hfields HsourcesAllocated HcellsAllocated HlocationsAllocated Hcoherent
 (packet_heap_valid _ _ _ _ _ _(packet_heap_allocation_frame _ _ _ _ _ _ _ _ _ Hpacket Halloc))
 (allocated_source_block_extent _ _ _ _ Halloc Hsize) Hregion HpacketRegion
 ltac:(auto) ltac:(intros;left;assumption) ltac:(auto))
 as (final & after & afterPackets & Hinit & Hcells & Hlocations & Hcoherent' & Hvalid & Hextent & Hregion' & HpacketRegion' & Hinc & Horigin & HpacketInc & HpacketOrigin & HfieldCoverage & Hviews).
 pose proof(typed_mixed_structure_names _ _ _ _ _ _ _ _ Htyped Hco) as Hnames.
 assert(Hmembers:forall field,In field fields ->source_member_type(field_slot_name field)(co_members co)=OK(field_slot_type field)).
 { intros field Hin;exact(proj1(proj2(proj2(proj1(Forall_forall _ _) Hfields field Hin)))). }
 assert(Hoffsets:forall field,In field fields ->field_offset(bcomposite_composite_env p.(prog_comp_env))(field_slot_name field)
 (bmembers_cmembers co.(co_members))=OK(field_slot_offset field,Full)).
 { intros field Hin;exact(proj1(proj2(proj2(proj2(proj1(Forall_forall _ _) Hfields field Hin))))). }
 assert(Hcoverage:forall delta ty chunk,scalar_object_leaf p.(prog_comp_env)(Stype sid attr) delta ty chunk ->
 exists stored,after fresh(Ptrofs.repr delta) ty stored /\transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk).
 { eapply complete_mixed_structure_scalar_coverage;eauto.
   eapply Forall_impl;[|exact HfieldCoverage];intros field Hfield;exact(proj1 Hfield). }
 assert(HpacketCoverage:forall delta,object_path p.(prog_comp_env)(Stype sid attr) delta Bytes ->afterPackets fresh(Ptrofs.repr delta)).
 { eapply complete_mixed_structure_packet_coverage;eauto.
   eapply Forall_impl;[|exact HfieldCoverage];intros field Hfield;exact(proj2 Hfield). }
 set(P':=copied_object_packets p.(prog_comp_env) packets(Stype sid attr) fresh).
 assert(Hequiv:forall b ofs,P' b ofs<->afterPackets b ofs).
 { intros b ofs;split.
   - intros [Hold|[Hb [delta [Hpath Ho]]]];[apply HpacketInc;exact Hold|subst;apply HpacketCoverage;exact Hpath].
   - intros Hin;destruct(HpacketOrigin _ _ Hin) as [Hold|[delta [Hb [Ho Hpath]]]];
     [left;exact Hold|right;split;[exact Hb|exists delta;auto]]. }
 destruct(initialized_structure_store_extension(globalenv p) p.(prog_comp_env) Gamma Sigma after m allocated final fresh sid attr pa
 _ _ _ Hblocks Halloc Hinit Hcells) as [Hext [Hblocks' [Hcells' Hvalue]]].
 set(Sigma':=PTree.set fresh(Ptrtype(Reftype(Bstruct sid attr)pa)) Sigma).
 assert(Hroot:object_type_at p.(prog_comp_env) Sigma' fresh 0(Stype sid attr)).
 { change(object_type_at p.(prog_comp_env) Sigma' fresh 0(stored_object_type(Ptrtype(Reftype(Bstruct sid attr)pa)))).
 apply object_type_root;[unfold Sigma';apply PTree.gss|exact(proj1 Hsize)]. }
 assert(HobjectApart:forall b base ty,objects b base ty ->b<>fresh).
 { intros b base ty Hin Heq;subst b;apply Hfresh.
 destruct(aggregate_object_readable _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hin)
 as [_ [_ [_ [Hb Hr]]]];exact Hb. }
 assert(Hmemory':initialized_object_memory(globalenv p) Sigma' final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after).
 { constructor.
 - assert(Hold:aggregate_objects_valid p.(prog_comp_env) Sigma' final objects).
   { eapply aggregate_objects_valid_frame;[exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hext| |].
     + intros;eapply field_initialization_preserves_valid_blocks;[exact Hinit|eapply Mem.valid_block_alloc;eauto].
     + intros;eapply field_initializer_preserves_permissions;[exact Hinit|eapply Mem.perm_alloc_1;eauto]. }
   constructor;intros b base ty [Hin|[Hb [Ho Ht]]].
   + eapply aggregate_object_typing;eauto.
   + subst;rewrite Ptrofs.unsigned_zero;exact Hroot.
   + eapply aggregate_object_readable;eauto.
   + subst;unfold aggregate_readable;rewrite Ptrofs.unsigned_zero.
     split;[reflexivity|]. split;[exact(proj1 Hsize)|]. split;[change(0+sizeof_type p.(prog_comp_env)(Stype sid attr)<=Ptrofs.modulus);unfold Ptrofs.max_unsigned in Hsize;lia|].
     split;[exact(source_extent_valid _ _ _ Hextent)|].
     intros ofs Hr;change(0<=ofs<0+sizeof_type p.(prog_comp_env)(Stype sid attr)) in Hr;
     eapply Mem.perm_implies;[apply(source_extent_freeable _ _ _ Hextent);lia|constructor].
   + eapply aggregate_object_address_bound;eauto.
   + subst;rewrite Ptrofs.unsigned_zero;change(0+sizeof_type p.(prog_comp_env)(Stype sid attr)<=Ptrofs.max_unsigned);lia.
 - intros b base root [Hin|[Hb [Ho Ht]]] delta ty ch Hleaf.
   + destruct(initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hin _ _ _ Hleaf) as [stored [Hcell Heq]].
     exists stored;split;[apply Hinc;exact Hcell|exact Heq].
   + subst;rewrite Ptrofs.unsigned_zero,Z.add_0_l;apply Hcoverage;exact Hleaf.
 - exact Hcells'.
 - intros b ofs ty ch Hin value Hread;eapply value_locations_monotone with(L:=descriptor_heap_locations(globalenv p) cells objects).
   + eapply descriptor_heap_locations_monotone;[exact Hinc|intros;left;assumption].
   + eapply packet_value_locations_nonbytes.
     * intro Heq;pose proof(typed_cell_access _ _ _ _ _ _ _(Hcells _ _ _ _ Hin)) as Hmode;rewrite Heq in Hmode;discriminate.
     * eapply Hlocations;eauto.
 - intros b base root [Hold|[Hb [Ho Ht]]] delta child Hpath.
   + intros cell ofs ty ch Hin;destruct(Horigin _ _ _ _ Hin) as [Hbefore|HfreshCell].
     * eapply initialized_object_scalar_coherence;eauto.
     * left;left;subst cell;intro Heq;symmetry in Heq;eapply HobjectApart;eauto.
   + subst;rewrite Ptrofs.unsigned_zero;eapply declared_scalar_region_hereditary;[exact Hregion'| |exact Hpath].
     unfold declared_leaf_separation;intros;eapply program_scalar_leaf_subobject;eauto. }
 assert(HpacketApart:packet_block_disjoint m packets fresh).
 { intros b ofs Hin;destruct(packet_heap_valid _ _ _ _ _ _ Hpacket _ _ Hin) as [_ [view [contents [Hdesc Hrest]]]]. split.
   - intro Heq;subst b;apply Hfresh;eapply packet_descriptor_source_block;eauto.
   - intros actual Hactual Heq;apply Hfresh;rewrite <-Heq;exact(proj1(proj2(proj2(proj2 Hactual)))). }
 assert(Hpacket':packet_heap_invariant(globalenv p) Sigma' final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after P').
 { eapply assemble_preallocated_object_packet_heap;[reflexivity|exact Hpacket|exact Hext|exact HobjectApart|exact HpacketApart|exact Horigin| |exact Hroot| | |].
   - intros delta child Hpath;replace delta with(0+delta) by lia;eapply declared_scalar_region_hereditary;[exact Hregion'| |exact Hpath].
     unfold declared_leaf_separation;intros;eapply program_scalar_leaf_subobject;eauto.
   - change(sizeof_type p.(prog_comp_env)(Stype sid attr)<=Ptrofs.modulus);unfold Ptrofs.max_unsigned in Hsize;lia.
   - eapply packet_state_valid_subcontext;[exact Hvalid|intros;apply Hequiv;assumption].
   - intros b ofs view Hin Hview;destruct(Hviews _ _ _ (proj1(Hequiv _ _) Hin) Hview) as [old [old_offset [Hold Hbefore]]].
     exists old,old_offset;split;[exact Hold|]. eapply packet_allocation_view_origin;[exact(packet_heap_valid _ _ _ _ _ _ Hpacket)|exact Halloc|exact Hold|exact Hbefore]. }
 assert(Hextents':heap_block_extents Sigma' final(add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after P').
 { eapply heap_extents_field_initializer;[|exact Hinit]. eapply heap_extents_allocation;[exact Hextents|exact Halloc|exact Hsize|].
   eapply tracked_data_block_same_block_extension.
   - intros;unfold Sigma' in *;eapply store_set_lookup_origin;eauto.
   - intros b base root [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb].
   - exact Horigin.
   - intros b ofs [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb]. }
 exists allocated,final,fresh,after;split;[reflexivity|]. split;[exact Hinit|]. split;[|exact Hcoherent'].
 constructor;try assumption;intros;try(left;assumption);assumption.
Qed.
