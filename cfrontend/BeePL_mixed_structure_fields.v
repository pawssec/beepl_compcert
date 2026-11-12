(* Heterogeneous evaluated field lists initialize one partially constructed
   parent. Argument source facts are fixed before writes into the fresh block. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_structure_field_planning BeePL_structure_initializer_slots BeePL_scalar_structure_coverage BeePL_structure_proofs BeePL_initializer_frames.
Require Import BeePL_object_paths BeePL_object_separation BeePL_packet_alignment BeePL_coherent_fields BeePL_layout_proofs.
Require Import BeePL_scalar_object_layout BeePL_scalar_object_coherence BeePL_layout_coherence.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_object_layout BeePL_packet_heap BeePL_packet_mutation.
Require Import BeePL_general_array_initialization BeePL_initializer_slot BeePL_initializer_determinism.
Require Import BeePL_structure_copy_regions BeePL_structure_copy_slots BeePL_declared_copy_field BeePL_block_extents BeePL_heap_extents BeePL_storage_types.
Import ListNotations.
Local Open Scope Z_scope.

Definition mixed_field_sources env seed packets m dst fields :=
 Forall(fun field=>(is_aggregate_type(field_slot_type field)=true \/ field_slot_type field=Bytes) ->
 array_copy_source env seed packets m dst(field_slot_type field)(field_slot_value field)) fields.

Lemma mixed_field_sources_frame : forall ge env seed packets m dst fields ty target value final result,
 mixed_field_sources env seed packets m dst fields ->
 assign_addr ge ty m dst target Full value final result ->
 mixed_field_sources env seed packets final dst fields.
Proof.
 intros * Hsources Hassign. eapply Forall_impl;[|exact Hsources]. intros field Hsource Hkind.
 destruct(Hsource Hkind) as [src source Hv Hapart Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
 eapply array_copy_source_intro with(src:=src)(source:=source);try assumption.
 - eapply assignment_preserves_valid_blocks;eauto.
 - intros position Hposition;eapply assignment_preserves_permissions;[exact Hassign|apply Hread;exact Hposition].
Qed.

Lemma evaluated_field_path : forall p Gamma Sigma L sid attr co field,
 PTree.get sid p.(prog_comp_env)=Some co ->
 evaluated_field_valid p Gamma Sigma L sid attr co field ->
 object_path p.(prog_comp_env)(Stype sid attr)(field_slot_offset field)(field_slot_type field).
Proof.
 intros * Hco [Ht [Hl [Hm [Ho [Hd [Hbound Hrest]]]]]].
 replace(field_slot_offset field) with(0+field_slot_offset field) by lia.
 eapply path_field with(co:=co)(field:=field_slot_name field).
 - constructor;apply source_size_nonnegative.
 - exact Hco.
 - unfold Ctyping.type_of_member;rewrite(source_member_type_translation _ _ _ Hm);reflexivity.
 - exact Hm.
 - exact Ho.
 - exact Hd.
 - apply source_size_nonnegative.
 - exact Hbound.
Qed.

Definition field_scalar_coverage env (cells : scalar_layout) (dst : Values.block) field : Prop :=
 forall delta ty chunk,scalar_object_leaf env(field_slot_type field) delta ty chunk ->
 exists stored,cells dst(Ptrofs.repr(field_slot_offset field+delta)) ty stored /\
 transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Definition field_packet_coverage env (packets : packet_locations) (dst : Values.block) field : Prop :=
 forall delta,object_path env(field_slot_type field) delta Bytes ->
 packets dst(Ptrofs.repr(field_slot_offset field+delta)).

Lemma scalar_field_leaf_identity : forall env root delta ty chunk cc,
 access_mode_type root=By_value cc ->scalar_object_leaf env root delta ty chunk ->
 delta=0 /\ ty=root.
Proof.
 intros * Hmode [Hpath HleafMode].
 exact(scalar_object_descent_identity _ _ _ _ _ _ Hmode(object_path_descent _ _ _ _ Hpath)).
Qed.

Lemma scalar_field_bytes_impossible : forall env root delta cc,
 access_mode_type root=By_value cc ->~object_path env root delta Bytes.
Proof.
 intros * Hmode Hpath.
 destruct(scalar_object_descent_identity _ _ _ _ _ _ Hmode(object_path_descent _ _ _ _ Hpath)) as [Hd Ht].
 subst root;discriminate Hmode.
Qed.

Theorem initialize_mixed_field : forall p Gamma Sigma L sid attr co field seed seedPackets cells packets m dst,
 PTree.get sid p.(prog_comp_env)=Some co ->storage_type_check p.(prog_comp_env)(Stype sid attr)=true ->
 evaluated_field_valid p Gamma Sigma L sid attr co field ->
 ((is_aggregate_type(field_slot_type field)=true \/ field_slot_type field=Bytes) ->
 array_copy_source p.(prog_comp_env) seed seedPackets m dst(field_slot_type field)(field_slot_value field)) ->
 typed_memory_layout p.(prog_comp_env) Sigma cells m ->memory_locations L cells m ->coherent_layout cells ->
 packet_state_valid m packets ->source_block_extent m dst(sizeof_type p.(prog_comp_env)(Stype sid attr)) ->
 scalar_object_region_coherent p.(prog_comp_env) cells dst 0(Stype sid attr) ->
 packet_object_region_coherent p.(prog_comp_env) m packets dst 0(Stype sid attr) ->
 (forall b ofs ty ch,seed b ofs ty ch ->cells b ofs ty ch) ->
 (forall b ofs ty ch,cells b ofs ty ch ->seed b ofs ty ch \/ b=dst) ->
 (forall b ofs,seedPackets b ofs ->packets b ofs) ->
 exists final after afterPackets,
 assign_addr(globalenv p)(field_slot_type field) m dst(Ptrofs.repr(field_slot_offset field)) Full(field_slot_value field) final(field_slot_value field) /\
 typed_memory_layout p.(prog_comp_env) Sigma after final /\memory_locations L after final /\coherent_layout after /\
 packet_state_valid final afterPackets /\source_block_extent final dst(sizeof_type p.(prog_comp_env)(Stype sid attr)) /\
 scalar_object_region_coherent p.(prog_comp_env) after dst 0(Stype sid attr) /\
 packet_object_region_coherent p.(prog_comp_env) final afterPackets dst 0(Stype sid attr) /\
 (forall b ofs ty ch,cells b ofs ty ch ->after b ofs ty ch) /\
 (forall b ofs ty ch,after b ofs ty ch ->cells b ofs ty ch \/ b=dst) /\
 (forall b ofs,packets b ofs ->afterPackets b ofs) /\
 (forall b ofs,afterPackets b ofs ->packets b ofs \/
   exists delta,b=dst /\ofs=Ptrofs.repr delta /\object_path p.(prog_comp_env)(Stype sid attr) delta Bytes) /\
 field_scalar_coverage p.(prog_comp_env) after dst field /\field_packet_coverage p.(prog_comp_env) afterPackets dst field /\
 (forall b ofs view,afterPackets b ofs ->packet_descriptor_valid final b ofs view ->
 exists old old_offset,packets old old_offset /\packet_descriptor_valid m old old_offset view).
Proof.
 intros * Hco Hstorage Hfield Hcopy Hcells Hlocations Hcoherent Hvalid Hextent Hregion HpacketRegion Hinc Horigin HpacketInc.
 pose proof(evaluated_field_path _ _ _ _ _ _ _ _ Hco Hfield) as Hpath.
 destruct Hfield as [Htyped [Hlocated [Hmember [Hoffset [Hdelta [Hinside [Hcomplete Hkind]]]]]]].
 pose proof(source_extent_bound _ _ _ Hextent) as Htotal.
 pose proof(storage_type_member_nonvolatile _ _ _ _ _ _ Hstorage Hco Hmember) as Hvol.
 assert(Hrepr:Ptrofs.unsigned(Ptrofs.repr(field_slot_offset field))=field_slot_offset field)
 by(apply Ptrofs.unsigned_repr;pose proof(source_size_nonnegative p.(prog_comp_env)(field_slot_type field));lia).
 destruct Hkind as [[chunk Hmode]|HcopyKind].
 - assert(Hleaf:scalar_object_leaf p.(prog_comp_env)(Stype sid attr)(field_slot_offset field)(field_slot_type field) chunk) by(split;assumption).
   pose proof(declared_scalar_packet_separation _ _ _ _ _ _ _ _ HpacketRegion Hleaf) as Hseparated.
   destruct(initialize_declared_scalar_slot p Gamma Sigma L cells packets m dst(Stype sid attr)
   (field_slot_offset field)(field_slot_type field) chunk(field_slot_value field)
   Htyped Hlocated Hvol Hcells Hlocations Hcoherent Hvalid Hextent Hregion Hleaf Hseparated)
   as [final [Hassign [Hcells' [Hlocations' [Hcoherent' [Hvalid' [Hextent' Hregion']]]]]]].
   assert(Hstore:Mem.store(transl_bchunk_cchunk chunk) m dst(field_slot_offset field)(trans_bvalue_cvalue(field_slot_value field))=Some final).
   { pose proof(proj2(full_assignment_computes _ _ _ _ _ _ _ _ Hassign)) as Hcompute.
     unfold full_assignment_memory in Hcompute;rewrite Hmode,Hrepr in Hcompute;exact Hcompute. }
   exists final,(extend_scalar_layout cells dst(Ptrofs.repr(field_slot_offset field))(field_slot_type field) chunk),packets.
   split;[exact Hassign|]. split;[exact Hcells'|]. split;[exact Hlocations'|]. split;[exact Hcoherent'|].
   split;[exact Hvalid'|]. split;[exact Hextent'|]. split;[exact Hregion'|]. split.
   + exact(scalar_store_packet_parent_region p.(prog_comp_env) m final packets dst(Stype sid attr) (field_slot_offset field)(transl_bchunk_cchunk chunk)(trans_bvalue_cvalue(field_slot_value field)) Hvalid HpacketRegion Hseparated Hstore).
   + split;[intros;left;assumption|]. split;[intros b ofs ty ch [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb]|].
     split;[auto|]. split;[intros;left;assumption|]. split.
     * intros delta ty ch Hleaf'. destruct(scalar_field_leaf_identity _ _ _ _ _ _ Hmode Hleaf') as [Hd Ht]. subst delta ty.
       exists chunk;split;[rewrite Z.add_0_r;right;auto|]. pose proof(proj2 Hleaf');congruence.
     * split;[intros delta Hbad;exfalso;eapply scalar_field_bytes_impossible;eauto|].
       intros b ofs view Hin Hview;exists b,ofs;split;[exact Hin|].
       eapply preserved_packet_view_origin;[exact Hvalid| |exact Hin|exact Hview].
       intros old offset Hpacket actual Hbefore;eapply packet_descriptor_store_frame;[exact Hstore|exact(proj1(Hseparated _ _ Hpacket))|exact Hbefore].
 - pose proof(Hcopy HcopyKind) as Hsource.
   destruct(initialize_declared_copy_field p Sigma L seed seedPackets cells packets m dst(Stype sid attr)
   (field_slot_offset field)(field_slot_type field)(field_slot_value field)
   Hpath HcopyKind Hsource Hcells Hlocations Hcoherent Hvalid Hextent Hregion HpacketRegion Hinc Horigin HpacketInc)
   as [src [source [final [bytes [Hv [Hread [Hstore [Hassign [Hcells' [Hlocations' [Hcoherent' [Hvalid' [Hextent' [Hregion' HpacketRegion']]]]]]]]]]]]]].
   exists final,(slot_copy_layout cells src(Ptrofs.unsigned source) dst(field_slot_offset field)(sizeof_type p.(prog_comp_env)(field_slot_type field))),
   (slot_copy_packets p.(prog_comp_env) packets(field_slot_type field) dst(field_slot_offset field)).
   split;[exact Hassign|]. split;[exact Hcells'|]. split;[exact Hlocations'|]. split;[exact Hcoherent'|].
   split;[exact Hvalid'|]. split;[exact Hextent'|]. split;[exact Hregion'|]. split;[exact HpacketRegion'|].
   split;[intros;left;assumption|]. split;[intros b ofs ty ch [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb]|].
   split;[intros;left;assumption|]. split.
   + intros b ofs [Hold|[Hb [delta [Hsub Ho]]]];[left;exact Hold|]. right;exists(field_slot_offset field+delta).
     split;[exact Hb|]. split;[exact Ho|]. eapply object_path_compose;eauto.
   + destruct Hsource as [original base Hv' Hneq HsourceValid HsourceBound HsourceAlign HsourceRead Hcoverage Hregions HpacketCoverage].
     assert(Hsame:original=src /\base=source) by(split;congruence);destruct Hsame as [Hb Ho];subst original base.
     split.
     * intros delta ty ch Hleaf. destruct(Hcoverage _ _ _ Hleaf) as [stored [Hcell Heq]]. exists stored;split;[|exact Heq].
       eapply slot_copy_covers_source_leaf;[apply Hinc;exact Hcell| | |].
       -- pose proof(Ptrofs.unsigned_range source);pose proof(scalar_object_leaf_bounds _ _ _ _ _ Hleaf);pose proof(size_chunk_pos(transl_bchunk_cchunk ch));
          apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia.
       -- exact(proj1(scalar_object_leaf_bounds _ _ _ _ _ Hleaf)).
       -- rewrite Heq;exact(proj2(proj2(scalar_object_leaf_bounds _ _ _ _ _ Hleaf))).
     * split;[intros delta Hsub;right;split;[reflexivity|exists delta;auto]|].
       intros b ofs view Hin Hview.
       eapply (replacement_slot_view_origin p.(prog_comp_env)(field_slot_type field) packets m final src(Ptrofs.unsigned source) dst(field_slot_offset field) bytes);try eassumption.
       -- apply source_size_nonnegative.
       -- pose proof(Ptrofs.unsigned_range source);lia.
       -- unfold Ptrofs.max_unsigned in Htotal;lia.
       -- intros;apply HpacketInc;apply HpacketCoverage;assumption.
       -- intros shift Hsub;eapply program_bytes_path_aligned;eapply object_path_compose;eauto.
       -- eapply declared_field_packet_replacement_plan;[pose proof(Ptrofs.unsigned_range source);lia|exact HsourceBound|exact Hvalid| |].
          ++ replace(field_slot_offset field) with(0+field_slot_offset field) by lia;eapply declared_packet_region_hereditary;eauto.
          ++ intros;apply HpacketInc;apply HpacketCoverage;assumption.
Qed.

Theorem initialize_mixed_structure_fields : forall fields p Gamma Sigma L sid attr co seed seedPackets cells packets m dst,
 PTree.get sid p.(prog_comp_env)=Some co ->storage_type_check p.(prog_comp_env)(Stype sid attr)=true ->
 Forall(evaluated_field_valid p Gamma Sigma L sid attr co) fields ->
 mixed_field_sources p.(prog_comp_env) seed seedPackets m dst fields ->
 typed_memory_layout p.(prog_comp_env) Sigma cells m ->memory_locations L cells m ->coherent_layout cells ->
 packet_state_valid m packets ->source_block_extent m dst(sizeof_type p.(prog_comp_env)(Stype sid attr)) ->
 scalar_object_region_coherent p.(prog_comp_env) cells dst 0(Stype sid attr) ->
 packet_object_region_coherent p.(prog_comp_env) m packets dst 0(Stype sid attr) ->
 (forall b ofs ty ch,seed b ofs ty ch ->cells b ofs ty ch) ->
 (forall b ofs ty ch,cells b ofs ty ch ->seed b ofs ty ch \/ b=dst) ->
 (forall b ofs,seedPackets b ofs ->packets b ofs) ->
 exists final after afterPackets,
 sem_allocate_fields(globalenv p) dst Ptrofs.zero sid(map field_slot_name fields)(map field_slot_value fields)(map field_slot_type fields) m final /\
 typed_memory_layout p.(prog_comp_env) Sigma after final /\memory_locations L after final /\coherent_layout after /\
 packet_state_valid final afterPackets /\source_block_extent final dst(sizeof_type p.(prog_comp_env)(Stype sid attr)) /\
 scalar_object_region_coherent p.(prog_comp_env) after dst 0(Stype sid attr) /\
 packet_object_region_coherent p.(prog_comp_env) final afterPackets dst 0(Stype sid attr) /\
 (forall b ofs ty ch,cells b ofs ty ch ->after b ofs ty ch) /\
 (forall b ofs ty ch,after b ofs ty ch ->cells b ofs ty ch \/ b=dst) /\
 (forall b ofs,packets b ofs ->afterPackets b ofs) /\
 (forall b ofs,afterPackets b ofs ->packets b ofs \/
 exists delta,b=dst /\ofs=Ptrofs.repr delta /\object_path p.(prog_comp_env)(Stype sid attr) delta Bytes) /\
 Forall(fun field=>field_scalar_coverage p.(prog_comp_env) after dst field /\field_packet_coverage p.(prog_comp_env) afterPackets dst field) fields /\
 (forall b ofs view,afterPackets b ofs ->packet_descriptor_valid final b ofs view ->
 exists old old_offset,packets old old_offset /\packet_descriptor_valid m old old_offset view).
Proof.
 induction fields as [|field fields IH];intros * Hco Hstorage Hfields Hsources Htyped Hlocated Hcoherent Hvalid Hextent Hregion HpacketRegion Hinc Horigin HpacketInc.
 - exists m,cells,packets. split;[constructor|]. split;[exact Htyped|]. split;[exact Hlocated|]. split;[exact Hcoherent|].
   split;[exact Hvalid|]. split;[exact Hextent|]. split;[exact Hregion|]. split;[exact HpacketRegion|].
   split;[auto|]. split;[intros;left;assumption|]. split;[auto|]. split;[intros;left;assumption|].
   split;[constructor|]. intros b ofs view Hin Hview;exists b,ofs;auto.
 - inversion Hfields as [|head tail Hfield Htail];subst head tail.
   inversion Hsources as [|head tail Hsource HsourceTail];subst head tail.
   destruct(initialize_mixed_field p Gamma Sigma L sid attr co field seed seedPackets cells packets m dst
   Hco Hstorage Hfield Hsource Htyped Hlocated Hcoherent Hvalid Hextent Hregion HpacketRegion Hinc Horigin HpacketInc)
   as (next & nextCells & nextPackets & Hassign & Htyped' & Hlocated' & Hcoherent' & Hvalid' & Hextent' & Hregion' & HpacketRegion' & Hinc' & Horigin' & HpacketInc' & HpacketOrigin' & Hcovered & HpacketCovered & Hviews).
   assert(Hsources':mixed_field_sources p.(prog_comp_env) seed seedPackets next dst fields)
   by(eapply mixed_field_sources_frame;[exact HsourceTail|exact Hassign]).
   destruct(IH p Gamma Sigma L sid attr co seed seedPackets nextCells nextPackets next dst
   Hco Hstorage Htail Hsources' Htyped' Hlocated' Hcoherent' Hvalid' Hextent' Hregion' HpacketRegion'
   ltac:(intros;apply Hinc';apply Hinc;assumption)
   ltac:(intros b ofs ty ch Hin;destruct(Horigin' _ _ _ _ Hin) as [Hold|Hb];[apply Horigin;exact Hold|right;exact Hb])
   ltac:(intros;apply HpacketInc';apply HpacketInc;assumption))
   as (final & after & afterPackets & Hinit & Htyped'' & Hlocated'' & Hcoherent'' & Hvalid'' & Hextent'' & Hregion'' & HpacketRegion'' & Hinc'' & Horigin'' & HpacketInc'' & HpacketOrigin'' & HcoveredTail & Hviews').
   exists final,after,afterPackets. split.
   + cbn [map]. eapply sem_allocate_struct with(co:=co)(delta:=field_slot_offset field)(bf:=Full).
     * exact Hco.
     * exact(proj1(proj2(proj2(proj2 Hfield)))).
     * rewrite Ptrofs.add_zero_l;exact Hassign.
     * exact Hinit.
   + split;[exact Htyped''|]. split;[exact Hlocated''|]. split;[exact Hcoherent''|]. split;[exact Hvalid''|].
     split;[exact Hextent''|]. split;[exact Hregion''|]. split;[exact HpacketRegion''|].
     split;[intros;apply Hinc'';apply Hinc';assumption|].
     split;[intros b ofs ty ch Hin;destruct(Horigin'' _ _ _ _ Hin) as [Hold|Hb];[apply Horigin';exact Hold|right;exact Hb]|].
     split;[intros;apply HpacketInc'';apply HpacketInc';assumption|].
     split;[intros b ofs Hin;destruct(HpacketOrigin'' _ _ Hin) as [Hold|Hnew];[apply HpacketOrigin';exact Hold|right;exact Hnew]|].
     split.
     * constructor;[split|exact HcoveredTail].
       -- intros delta ty ch Hleaf;destruct(Hcovered _ _ _ Hleaf) as [stored [Hcell Heq]]. exists stored;split;[apply Hinc'';exact Hcell|exact Heq].
       -- intros delta Hpath;apply HpacketInc'';apply HpacketCovered;exact Hpath.
     * intros b ofs view Hin Hview;destruct(Hviews' _ _ _ Hin Hview) as [old [old_offset [Hold Hbefore]]].
       eapply Hviews;eauto.
Qed.

Print Assumptions initialize_mixed_structure_fields.
