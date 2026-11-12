(* Scalar field initialization establishes the shared heap, including pointer
   fields and repeated exact aliases. Slot metadata is supplied by checked
   source planning, never by a post-state assumption. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_structure_initializer_slots BeePL_scalar_structure_coverage BeePL_structure_field_planning.
Require Import BeePL_structure_storage_typing BeePL_structure_proofs BeePL_initialized_structures.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory BeePL_scalar_object_layout.
Require Import BeePL_callable_array_objects BeePL_initializer_coherence BeePL_object_separation.
Require Import BeePL_packet_heap BeePL_packet_state BeePL_packet_mutation BeePL_packet_bindings BeePL_packet_coverage.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_storage_types BeePL_heap_extents BeePL_block_extents.
Require Import BeePL_fresh_copy BeePL_initializer_frames BeePL_layout_coherence BeePL_initialized_runtime.
Require Import BeePL_copy_array_heap BeePL_coherent_fields BeePL_initialized_call_entry.
Import ListNotations.
Local Open Scope Z_scope.

Theorem initialize_scalar_structure_heap : forall p Gamma Sigma vm m objects cells packets sid attr pa co slots result ef,
 initialized_heap_state(globalenv p) Gamma Sigma vm m objects cells packets -> coherent_layout cells ->
 type_expr p.(prog_comp_env) Gamma Sigma(Sinit sid(map scalar_field_name slots)(map scalar_slot_expression slots) result) ef result ->
 structure_result_type sid attr result -> PTree.get sid p.(prog_comp_env)=Some co ->
 Forall(fun slot=>value_locations(packet_heap_locations(globalenv p) cells objects packets)
 (scalar_field_value slot)(scalar_field_type slot)) slots ->
 (forall slot,In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 (forall slot,In slot slots -> field_offset(bcomposite_composite_env p.(prog_comp_env))(scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 exists allocated final fresh after,
 Mem.alloc m 0(sizeof_type p.(prog_comp_env)(Stype sid attr))=(allocated,fresh) /\
 sem_allocate_fields(globalenv p) fresh Ptrofs.zero sid(map scalar_field_name slots)
 (map scalar_field_value slots)(map scalar_field_type slots) allocated final /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets
 (PTree.set fresh(Ptrtype(Reftype(Bstruct sid attr)pa)) Sigma) final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after packets /\ coherent_layout after.
Proof.
 intros * Hheap Hcoherent Htyped Hshape Hco Hvalues Hmodes Hoffsets.
 destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
 pose proof(typed_structure_storage_admissible _ _ _ _ _ _ _ _ _ Htyped Hshape) as Hstorage.
 pose proof(storage_type_size_bounds _ _ Hstorage) as Hsize.
 destruct(Mem.alloc m 0(sizeof_type p.(prog_comp_env)(Stype sid attr))) as [allocated fresh] eqn:Halloc.
 pose proof(Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hfresh.
 assert(HcellsAllocated:typed_memory_layout p.(prog_comp_env) Sigma cells allocated).
 { intros b ofs ty ch Hin;eapply typed_memory_cell_alloc_frame;
 [exact Halloc|exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)]. }
 assert(HlocationsAllocated:memory_locations(descriptor_heap_locations(globalenv p) cells objects) cells allocated).
 { eapply allocation_memory_locations;[exact(initialized_object_cells _ _ _ _ _ Hmemory)|
 exact(initialized_object_locations _ _ _ _ _ Hmemory)|exact Halloc]. }
 assert(Hvalues':Forall(fun slot=>value_locations(descriptor_heap_locations(globalenv p) cells objects)
 (scalar_field_value slot)(scalar_field_type slot)) slots).
 { apply Forall_forall;intros slot Hin. eapply packet_value_locations_nonbytes.
 - intro Heq;pose proof(Hmodes slot Hin);rewrite Heq in H;discriminate.
 - apply(proj1(Forall_forall _ _) Hvalues slot Hin). }
 assert(HcellApart:forall b ofs ty ch,cells b ofs ty ch -> b<>fresh).
 { intros b ofs ty ch Hin Heq;subst b;apply Hfresh;eapply initialized_scalar_valid_block;
 eapply typed_memory_cell_erasure;exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin). }
 assert(Hregion:scalar_object_region_coherent p.(prog_comp_env) cells fresh 0(Stype sid attr)).
 { intros b ofs ty ch Hin;left;left;eapply HcellApart;exact Hin. }
 destruct(initialize_typed_scalar_structure_fields p Gamma Sigma _ sid attr co slots result ef cells packets allocated fresh
 Htyped Hshape Hco Hvalues' Hmodes Hoffsets HcellsAllocated HlocationsAllocated Hcoherent
 (packet_heap_valid _ _ _ _ _ _(packet_heap_allocation_frame _ _ _ _ _ _ _ _ _ Hpacket Halloc))
 (allocated_packet_block_disjoint _ _ _ _ _ _(packet_heap_valid _ _ _ _ _ _ Hpacket) Halloc)
 (allocated_source_block_extent _ _ _ _ Halloc Hsize) Hregion)
 as [final [after [Hinit [Hcells [Hlocations [Hcoherent' [Hvalid [Hdisjoint [Hextent [Hregion' [Hinc [Hcoverage Horigin]]]]]]]]]]]].
 assert(HoriginCells:forall b ofs ty ch,after b ofs ty ch ->cells b ofs ty ch \/ b=fresh).
 { intros b ofs ty ch Hin;destruct(Horigin _ _ _ _ Hin) as [Hold|[slot [Hslot [Hb Hrest]]]];[left;exact Hold|right;exact Hb]. }
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
   + subst. unfold aggregate_readable;rewrite Ptrofs.unsigned_zero.
     split;[reflexivity|]. split;[exact(proj1 Hsize)|]. split;[change (0+sizeof_type p.(prog_comp_env)(Stype sid attr)<=Ptrofs.modulus); unfold Ptrofs.max_unsigned in Hsize;lia|].
     split;[exact(source_extent_valid _ _ _ Hextent)|].
     intros ofs Hr;change (0<=ofs<0+sizeof_type p.(prog_comp_env)(Stype sid attr)) in Hr;eapply Mem.perm_implies;[apply(source_extent_freeable _ _ _ Hextent);lia|constructor].
   + eapply aggregate_object_address_bound;eauto.
   + subst;rewrite Ptrofs.unsigned_zero;change (0+sizeof_type p.(prog_comp_env)(Stype sid attr)<=Ptrofs.max_unsigned);lia.
 - intros b base root [Hin|[Hb [Ho Ht]]] delta ty ch Hleaf.
   + destruct(initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hin _ _ _ Hleaf) as [stored [Hcell Heq]].
     exists stored;split;[apply Hinc;exact Hcell|exact Heq].
   + subst;rewrite Ptrofs.unsigned_zero,Z.add_0_l;apply Hcoverage;exact Hleaf.
 - exact Hcells'.
 - intros b ofs ty ch Hin v Hread;eapply value_locations_monotone;[|eapply Hlocations;eauto].
   eapply descriptor_heap_locations_monotone;[exact Hinc|intros;left;assumption].
 - intros b base root [Hold|[Hb [Ho Ht]]] delta child Hpath.
   + intros cell ofs ty ch Hin;destruct(HoriginCells _ _ _ _ Hin) as [Hbefore|HfreshCell].
     * eapply initialized_object_scalar_coherence;eauto.
     * left;left;subst cell;intro Heq;symmetry in Heq;eapply HobjectApart;eauto.
   + subst;rewrite Ptrofs.unsigned_zero. eapply declared_scalar_region_hereditary;[exact Hregion'| |exact Hpath].
     unfold declared_leaf_separation;intros;eapply program_scalar_leaf_subobject;eauto. }
 assert(Hpacket':packet_heap_invariant(globalenv p) Sigma' final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after packets).
 { eapply packet_heap_fresh_field_elements;[exact Hpacket|exact Hext|exact Halloc|exact Hinit| |exact HoriginCells].
 intros delta Hpath. unfold bytes_object_leaf in Hpath.
 destruct(typed_scalar_structure_slot_facts _ _ _ _ _ _ _ _ _ _ Htyped Hshape Hco Hvalues' Hmodes Hoffsets)
 as [Hslots [Hnames Hmembers]].
 destruct(complete_scalar_struct_paths _ _ _ _ _ Hco Hnames Hmembers Hoffsets Hmodes _ _ Hpath)
 as [[Hd Ht]|[slot [Hin [Hd Ht]]]];[discriminate Ht|].
 pose proof(Hmodes slot Hin) as Hmode;rewrite <-Ht in Hmode;discriminate. }
 assert(Hextents':heap_block_extents Sigma' final
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)) after packets).
 { eapply heap_extents_field_initializer;[|exact Hinit].
   eapply heap_extents_allocation;[exact Hextents|exact Halloc|exact Hsize|].
   eapply tracked_data_block_same_block_extension.
   - intros;unfold Sigma' in *;eapply store_set_lookup_origin;eauto.
   - intros b base root [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb].
   - exact HoriginCells.
   - intros;left;assumption. }
 exists allocated,final,fresh,after. split;[reflexivity|]. split;[exact Hinit|]. split;[|exact Hcoherent'].
 constructor;try assumption;intros;try(left;assumption);assumption.
Qed.

Print Assumptions initialize_scalar_structure_heap.

Require Import BeePL_coherent_configurations BeePL_auxlemmas BeePL_structure_object_coverage.
Lemma scalar_slot_expression_extract : forall slots,
 extract_values_exprs(map scalar_slot_expression slots)=map scalar_field_value slots /\
 typeof_exprs(map scalar_slot_expression slots)=map scalar_field_type slots.
Proof. induction slots as [|slot slots [Hvalues Htypes]]; [split; reflexivity|].
 split; simpl; congruence. Qed.

Theorem scalar_structure_configuration_progress : forall p Gamma Sigma vm m objects cells packets sid attr co slots result ef,
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets
 (Sinit sid(map scalar_field_name slots)(map scalar_slot_expression slots) result) ef result ->
 structure_result_type sid attr result -> PTree.get sid p.(prog_comp_env)=Some co ->
 (forall slot,In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 (forall slot,In slot slots -> field_offset(bcomposite_composite_env p.(prog_comp_env))(scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 exists final fresh Sigma' objects' after,
 ssem_expr(globalenv p) p vm m(Sinit sid(map scalar_field_name slots)(map scalar_slot_expression slots) result)
 final vm(Val(Vloc fresh Ptrofs.zero) result) /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' after packets /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm final objects' after packets
 (Val(Vloc fresh Ptrofs.zero) result) nil result.
Proof.
 intros * Hconfig Hshape Hco Hmodes Hoffsets.
 pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
 assert(Hvalues:Forall(fun slot=>value_locations(packet_heap_locations(globalenv p) cells objects packets)
 (scalar_field_value slot)(scalar_field_type slot)) slots).
 { change(all_expr_locations(runtime_locations(packet_heap_locations(globalenv p) cells objects packets))
 (map scalar_slot_expression slots)) in Hlocations.
 apply all_expr_locations_Forall in Hlocations. apply Forall_forall;intros slot Hin.
 apply(proj1(Forall_forall _ _) Hlocations (scalar_slot_expression slot));apply in_map;exact Hin. }
 assert(Hpa:exists pa,result=Stype sid attr \/ result=Ptrtype(Reftype(Bstruct sid attr)pa)).
 { destruct Hshape as [Heq|[pa Heq]];[exists noattr;left|exists pa;right];exact Heq. }
 destruct Hpa as [pa Hresult].
 destruct(initialize_scalar_structure_heap p Gamma Sigma vm m objects cells packets sid attr pa co slots result ef
 Hheap Hcoherent Htyped Hshape Hco Hvalues Hmodes Hoffsets)
 as [allocated [final [fresh [after [Halloc [Hinit [Hevolution Hcoherent']]]]]]].
 exists final,fresh,(PTree.set fresh(Ptrtype(Reftype(Bstruct sid attr)pa)) Sigma),
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)),after.
 split.
 - eapply ssem_sinit2 with(sa:=attr)(allocated:=allocated);[exact Hshape| |exact Halloc|].
   + apply Forall_forall;intros e Hin;apply in_map_iff in Hin;destruct Hin as [slot [<- Hin]].
     exists(scalar_field_value slot),(scalar_field_type slot);reflexivity.
   + destruct(scalar_slot_expression_extract slots) as [Hvs Hts];rewrite Hvs,Hts;exact Hinit.
 - split;[exact Hevolution|]. split;[|exact Hcoherent'].
   pose proof(initialized_runtime_configuration_evolve _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig) Hevolution) as Hconfigured.
   destruct Hconfigured as [Hheap' Htyped' Hlocated' Hframes'].
   constructor;[exact Hheap'| | |exact I].
   + destruct Hresult as [Heq|Heq]; subst result.
     * apply ty_valstruct. eapply aggregate_object_typing;
       [exact(initialized_object_descriptors _ _ _ _ _(initialized_heap_memory _ _ _ _ _ _ _ _ Hheap'))|right;auto].
     * apply ty_valloc;apply PTree.gss.
   + destruct Hresult as [Heq|Heq]; subst result;simpl;left;right.
     * left;split;[reflexivity|right;auto].
     * right;exists(Bstruct sid attr),pa;split;[reflexivity|]. split;[reflexivity|right;auto].
Qed.

Theorem evaluated_scalar_structure_progress : forall p Gamma Sigma vm m objects cells packets sid attr ids es result ef,
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets(Sinit sid ids es result) ef result ->
 structure_result_type sid attr result ->
 Forall(fun e=>exists v ty,e=Val v ty) es ->
 Forall(fun e=>is_aggregate_type(typeof_expr e)=false /\ typeof_expr e<>Bytes) es ->
 exists final fresh Sigma' objects' after,
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) final vm(Val(Vloc fresh Ptrofs.zero) result) /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' after packets /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm final objects' after packets
 (Val(Vloc fresh Ptrofs.zero) result) nil result.
Proof.
 intros * Hconfig Hshape Hvalues Hscalar.
 pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
 assert(Hlocated:Forall(fun e=>exists v ty,e=Val v ty /\ value_locations(packet_heap_locations(globalenv p) cells objects packets) v ty) es).
 { change(all_expr_locations(runtime_locations(packet_heap_locations(globalenv p) cells objects packets)) es) in Hlocations.
 apply all_expr_locations_Forall in Hlocations. apply Forall_forall;intros e Hin.
 destruct(proj1(Forall_forall _ _) Hvalues e Hin) as [v [ty Heq]].
 exists v,ty;split;[exact Heq|]. subst e;exact(proj1(Forall_forall _ _) Hlocations _ Hin). }
 destruct(typed_structure_field_plan _ _ _ _ _ _ _ _ _ _ Htyped Hshape Hlocated)
 as [co [fields [Hco [Hnames [Hexprs Hvalid]]]]].
 assert(HscalarFields:Forall(fun field=>is_aggregate_type(field_slot_type field)=false /\ field_slot_type field<>Bytes) fields).
 { apply Forall_forall;intros field Hin.
 pose proof(proj1(Forall_forall _ _) Hscalar (field_slot_expression field)
 ltac:(rewrite <-Hexprs;apply in_map;exact Hin)) as Hkind.
 exact Hkind. }
 destruct(scalarize_evaluated_field_plan _ _ _ _ _ _ _ _ Hvalid HscalarFields)
 as [slots [HslotNames [HslotExprs [Hmodes Hoffsets]]]].
 rewrite Hnames in HslotNames;rewrite Hexprs in HslotExprs.
 rewrite <-HslotNames,<-HslotExprs in Hconfig |- *.
 eapply scalar_structure_configuration_progress; eauto.
Qed.

Print Assumptions evaluated_scalar_structure_progress.
