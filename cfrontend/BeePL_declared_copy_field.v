(* Construct a real copy into a declared field of a partially initialized
   parent, deriving readiness and alias plans from source and parent facts. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations BeePL_object_paths.
Require Import BeePL_scalar_object_layout BeePL_scalar_object_coherence BeePL_object_separation BeePL_packet_alignment BeePL_callable_array_objects BeePL_initializer_coherence.
Require Import BeePL_initializer_slot BeePL_general_array_initialization BeePL_layout_coherence BeePL_copy_cells.
Require Import BeePL_structure_copy_slots BeePL_compatible_copy_slot BeePL_structure_copy_regions.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_object_layout BeePL_packet_replacement.
Require Import BeePL_block_extents BeePL_heap_extents.
Local Open Scope Z_scope.

Lemma program_declared_copy_alignment : forall p parent delta root,
 object_path p.(prog_comp_env) parent delta root ->
 ((if is_bytes root then align_chunk Mptr else alignof_blockcopy(bcomposite_composite_env p.(prog_comp_env))(transBeePL_type root))|delta).
Proof.
 intros * Hpath. destruct(is_bytes root) eqn:Hbytes.
 - assert(root=Bytes) by(destruct root;try discriminate;reflexivity);subst root.
   exact(program_bytes_path_aligned p parent delta Hpath).
 - rewrite program_blockcopy_natural_alignment.
   eapply Z.divide_trans;[apply minimum_blockcopy_alignment_divides|
   exact(proj1(program_object_path_alignment _ _ _ _ Hpath _ (natural_object_alignment_power _ _)(Z.le_refl _)))].
Qed.

Theorem initialize_declared_copy_field : forall p Sigma L seed seedPackets cells packets m dst parent delta root value,
 object_path p.(prog_comp_env) parent delta root ->
 is_aggregate_type root=true \/ root=Bytes ->
 array_copy_source p.(prog_comp_env) seed seedPackets m dst root value ->
 typed_memory_layout p.(prog_comp_env) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
 packet_state_valid m packets -> source_block_extent m dst(sizeof_type p.(prog_comp_env) parent) ->
 scalar_object_region_coherent p.(prog_comp_env) cells dst 0 parent ->
 packet_object_region_coherent p.(prog_comp_env) m packets dst 0 parent ->
 (forall b ofs ty ch,seed b ofs ty ch ->cells b ofs ty ch) ->
 (forall b ofs ty ch,cells b ofs ty ch ->seed b ofs ty ch \/ b=dst) ->
 (forall b ofs,seedPackets b ofs ->packets b ofs) ->
 exists src source final bytes,
 value=Vloc src source /\
 Mem.loadbytes m src(Ptrofs.unsigned source)(sizeof_type p.(prog_comp_env) root)=Some bytes /\
 Mem.storebytes m dst delta bytes=Some final /\
 assign_addr(globalenv p) root m dst(Ptrofs.repr delta) Full value final value /\
 let after:=slot_copy_layout cells src(Ptrofs.unsigned source) dst delta(sizeof_type p.(prog_comp_env) root) in
 let afterPackets:=slot_copy_packets p.(prog_comp_env) packets root dst delta in
 typed_memory_layout p.(prog_comp_env) Sigma after final /\ memory_locations L after final /\ coherent_layout after /\
 packet_state_valid final afterPackets /\ source_block_extent final dst(sizeof_type p.(prog_comp_env) parent) /\
 scalar_object_region_coherent p.(prog_comp_env) after dst 0 parent /\
 packet_object_region_coherent p.(prog_comp_env) final afterPackets dst 0 parent.
Proof.
 intros * Hpath Hkind Hsource Hcells Hlocations Hcoherent Hvalid Hextent Hregion HpacketRegion Hinc Horigin HpacketInc.
 destruct Hsource as [src source Hv Hneq HsourceValid HsourceBound HsourceAlign Hread Hcoverage Hregions HpacketCoverage].
 pose proof(object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hsize Hinside]].
 pose proof(source_extent_bound _ _ _ Hextent) as HparentSize.
 assert(Hrepr:Ptrofs.unsigned(Ptrofs.repr delta)=delta) by(apply Ptrofs.unsigned_repr;lia).
 assert(HtargetRegion:scalar_object_region_coherent p.(prog_comp_env) cells dst delta root).
 { replace delta with(0+delta) by lia;eapply declared_scalar_region_hereditary;[exact Hregion| |exact Hpath].
 unfold BeePL_initializer_coherence.declared_leaf_separation;intros;eapply program_scalar_leaf_subobject;eauto. }
 assert(HtargetPacket:packet_object_region_coherent p.(prog_comp_env) m packets dst delta root).
 { replace delta with(0+delta) by lia;eapply declared_packet_region_hereditary;eauto. }
 assert(HsourceRegion:0<sizeof_type p.(prog_comp_env) root ->scalar_object_region_coherent p.(prog_comp_env) cells src(Ptrofs.unsigned source) root).
 { intros Hpositive. replace(Ptrofs.unsigned source) with(Ptrofs.unsigned source+0) by lia.
 eapply array_current_source_regions;[exact Hneq|exact Horigin|apply Hregions;exact Hpositive|constructor;exact Hsize]. }
 assert(HsourceCells:forall shift ty ch,scalar_object_leaf p.(prog_comp_env) root shift ty ch ->
 exists stored,cells src(Ptrofs.repr(Ptrofs.unsigned source+shift)) ty stored /\transl_bchunk_cchunk stored=transl_bchunk_cchunk ch).
 { intros shift ty ch Hleaf;destruct(Hcoverage _ _ _ Hleaf) as [stored [Hcell Hchunk]]. exists stored;split;[apply Hinc;exact Hcell|exact Hchunk]. }
 assert(Halignment:slot_copy_alignment cells src(Ptrofs.unsigned source) delta(sizeof_type p.(prog_comp_env) root)).
 { intros old ty ch shift Hcell Ho Hshift Hbound.
 pose proof(size_chunk_pos(transl_bchunk_cchunk ch)).
 destruct(HsourceRegion ltac:(lia) _ _ _ _ Hcell) as [[Hbad|[Hbefore|Hafter]]|[leaf [[Hleaf Hmode] [Hb Hofs]]]];try contradiction;try lia.
 assert(leaf=shift) by lia;subst leaf. eapply program_scalar_object_leaf_alignment.
 split;[eapply object_path_compose;eauto|exact Hmode]. }
 assert(HpacketAlignment:forall shift,object_path p.(prog_comp_env) root shift Bytes ->(align_chunk Mptr|delta+shift)).
 { intros shift Hleaf;eapply program_bytes_path_aligned;eapply object_path_compose;eauto. }
 assert(Hready:initializer_copy_ready(globalenv p) m root src source dst(Ptrofs.repr delta)).
 { constructor;try assumption;rewrite ?Hrepr.
 - exact(source_extent_valid _ _ _ Hextent).
 - change(delta+sizeof_type p.(prog_comp_env) root<=Ptrofs.modulus);unfold Ptrofs.max_unsigned in HparentSize;lia.
 - exact(program_declared_copy_alignment p parent delta root Hpath).
 - left;exact Hneq.
 - intros ofs Hin;change(delta<=ofs<delta+sizeof_type p.(prog_comp_env) root) in Hin;apply(source_extent_freeable _ _ _ Hextent);lia. }
 destruct(initialize_compatible_copy_slot(globalenv p) Sigma L cells packets m root src source dst(Ptrofs.repr delta)
 Hready Hcells Hlocations ltac:(rewrite Hrepr;exact HtargetRegion) HsourceCells
 ltac:(rewrite Hrepr;exact Halignment) Hvalid ltac:(intros;apply HpacketInc;apply HpacketCoverage;assumption)
 ltac:(rewrite Hrepr;exact HpacketAlignment) ltac:(rewrite Hrepr;exact HtargetPacket))
 as [final [bytes [Hload [Hstore [Hassign [Hcells' [Hlocations' Hvalid']]]]]]].
 rewrite Hrepr in Hstore,Hcells',Hlocations',Hvalid'.
 assert(Hplan:scalar_copy_plan cells(slot_copy_layout cells src(Ptrofs.unsigned source) dst delta(sizeof_type p.(prog_comp_env) root))
 src(Ptrofs.unsigned source) dst delta(sizeof_type p.(prog_comp_env) root)).
 { eapply declared_field_copy_layout_plan;eauto;pose proof(Ptrofs.unsigned_range source);unfold Ptrofs.max_unsigned in HparentSize;lia. }
 assert(HpacketPlan:packet_copy_replacement_plan m packets src(Ptrofs.unsigned source) dst delta(sizeof_type p.(prog_comp_env) root)).
 { eapply declared_field_packet_replacement_plan;eauto;pose proof(Ptrofs.unsigned_range source);lia. }
 exists src,source,final,bytes;split;[exact Hv|]. split;[exact Hload|]. split;[exact Hstore|].
 split;[rewrite Hv;exact Hassign|]. cbn zeta.
 split;[exact Hcells'|]. split;[exact Hlocations'|]. split;[eapply scalar_copy_plan_coherent;eauto|].
 split;[exact Hvalid'|]. split;[eapply assignment_source_extent;eauto|]. split.
 - eapply copied_declared_parent_region;eauto;lia.
 - eapply (copied_declared_packet_parent_region p parent root delta packets m final src(Ptrofs.unsigned source) dst bytes);eauto;try(pose proof(Ptrofs.unsigned_range source);lia).
Qed.
