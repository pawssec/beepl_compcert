(* Partial struct initialization keeps declared regions for the parent,
   even before every field is initialized and parent coverage can be claimed. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_object_paths.
Require Import BeePL_scalar_object_layout BeePL_scalar_object_coherence BeePL_object_separation.
Require Import BeePL_callable_array_objects BeePL_initializer_coherence BeePL_initializer_slot.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_coverage.
Require Import BeePL_packet_replacement BeePL_compatible_copy_slot BeePL_bytes_execution BeePL_packet_mutation.
Local Open Scope Z_scope.

Theorem copied_declared_parent_region : forall env cells src source dst parent delta root,
 scalar_object_region_coherent env cells dst 0 parent ->
 object_path env parent delta root -> sizeof_type env parent<=Ptrofs.max_unsigned ->
 (0<sizeof_type env root -> scalar_object_region_coherent env cells src source root) ->
 scalar_object_region_coherent env
 (slot_copy_layout cells src source dst delta(sizeof_type env root)) dst 0 parent.
Proof.
 intros * Hparent Hpath Hbound Hsource b ofs ty chunk [Hold|[Hb [old [shift [Hcell [Ho [Hs [Hinside Heq]]]]]]]].
 - eapply Hparent;exact Hold.
 - subst b ofs. pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [Hr Htotal]].
   pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
   destruct(Hsource ltac:(lia) _ _ _ _ Hcell) as [[Hneq|[Hbefore|Hafter]]|[leaf [Hleaf [Hb Ho']]]];try contradiction;try lia.
   assert(leaf=shift) by lia;subst leaf.
   right;exists(delta+shift). split.
   + destruct Hleaf as [Hleaf Hmode];split;[eapply object_path_compose;eauto|exact Hmode].
   + split;[reflexivity|]. rewrite Ptrofs.unsigned_repr;lia.
Qed.

Theorem copied_declared_parent_regions : forall p cells src source dst parent delta root,
 scalar_object_region_coherent p.(prog_comp_env) cells dst 0 parent ->
 object_path p.(prog_comp_env) parent delta root -> sizeof_type p.(prog_comp_env) parent<=Ptrofs.max_unsigned ->
 (0<sizeof_type p.(prog_comp_env) root ->scalar_object_region_coherent p.(prog_comp_env) cells src source root) ->
 forall child_offset child,object_path p.(prog_comp_env) parent child_offset child ->
 scalar_object_region_coherent p.(prog_comp_env)
 (slot_copy_layout cells src source dst delta(sizeof_type p.(prog_comp_env) root)) dst child_offset child.
Proof.
 intros * Hparent Hfield Hbound Hsource child_offset child Hchild.
 replace child_offset with(0+child_offset) by lia.
 eapply declared_scalar_region_hereditary;[eapply copied_declared_parent_region;eauto| |exact Hchild].
 unfold declared_leaf_separation;intros;eapply program_scalar_leaf_subobject;eauto.
Qed.

Theorem replacement_slot_view_origin : forall env root packets m final src source dst target bytes,
 0<=sizeof_type env root -> 0<=source ->source+sizeof_type env root<=Ptrofs.modulus ->
 0<=target ->target+sizeof_type env root<=Ptrofs.modulus ->
 packet_state_valid m packets ->
 (forall delta,object_path env root delta Bytes ->packets src(Ptrofs.repr(source+delta))) ->
 (forall delta,object_path env root delta Bytes ->(align_chunk Mptr|target+delta)) ->
 packet_copy_replacement_plan m packets src source dst target(sizeof_type env root) ->
 Mem.loadbytes m src source(sizeof_type env root)=Some bytes ->
 Mem.storebytes m dst target bytes=Some final ->
 forall b ofs view,slot_copy_packets env packets root dst target b ofs ->
 packet_descriptor_valid final b ofs view ->
 exists old old_offset,packets old old_offset /\ packet_descriptor_valid m old old_offset view.
Proof.
 intros * Hsize Hsource HsourceEnd Htarget HtargetEnd Hvalid Hcoverage Halign Hplan Hread Hstore b ofs view Hin Hview.
 destruct Hin as [Hold|[Hb [delta [Hpath Ho]]]].
 - eapply(proj2(packet_copy_replacement_state _ _ _ _ _ _ _ _ _ Hsize Hvalid Hplan Hread Hstore));eauto.
 - subst b ofs. pose proof(Hcoverage _ Hpath) as HsourcePacket.
   destruct(Hvalid _ _ HsourcePacket) as [_ [actual [contents [Hdescriptor Hcontents]]]].
   assert(Hcopied:packet_descriptor_valid final dst(Ptrofs.repr(target+delta)) actual).
   { eapply (slot_copied_descriptor env root m final src source dst target bytes delta actual);eauto. }
   assert(view=actual) by(eapply packet_descriptor_view_unique;eauto);subst view.
   exists src,(Ptrofs.repr(source+delta));auto.
Qed.

Require Import BeePL_object_edges BeePL_packet_object_layout BeePL_packet_heap.
Lemma bytes_object_descent_identity : forall env base offset child,
 object_descent env base Bytes offset child ->offset=base /\ child=Bytes.
Proof.
 intros * Hpath;inversion Hpath;subst;[auto|].
 match goal with Hedge:object_edge _ _ _ |- _ =>inversion Hedge end.
Qed.

Lemma program_bytes_leaf_subobject : forall p root leaf child_offset child,
 object_path p.(prog_comp_env) root leaf Bytes ->
 object_path p.(prog_comp_env) root child_offset child ->
 (leaf+packet_descriptor_size<=child_offset \/ child_offset+sizeof_type p.(prog_comp_env) child<=leaf) \/
 exists relative,object_path p.(prog_comp_env) child relative Bytes /\ leaf=child_offset+relative.
Proof.
 intros * Hleaf Hchild.
 destruct(program_object_descents_separate_or_nested _ _ _ _ _ _ _
 (object_path_descent _ _ _ _ Hleaf)(object_path_descent _ _ _ _ Hchild))
 as [Hbefore|[Hafter|[Hdown|Hup]]].
 - left;left;exact Hbefore.
 - left;right;exact Hafter.
 - destruct(bytes_object_descent_identity _ _ _ _ Hdown) as [Ho Ht];subst child_offset child.
   right;exists 0;split;[constructor;apply object_source_size_nonnegative|lia].
 - right;exists(leaf-child_offset);split;[eapply object_descent_as_path;exact Hup|lia].
Qed.

Theorem declared_packet_region_hereditary : forall p m packets dst start root,
 packet_object_region_coherent p.(prog_comp_env) m packets dst start root ->
 forall delta child,object_path p.(prog_comp_env) root delta child ->
 packet_object_region_coherent p.(prog_comp_env) m packets dst(start+delta) child.
Proof.
 intros * Hroot delta child Hpath descriptor offset Hin.
 destruct(Hroot _ _ Hin) as [Hdescriptor Hpayload].
 pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [Hs Hinside]]. split.
 - destruct Hdescriptor as [Haway|[leaf [Hleaf [Hb Ho]]]].
   + left;eapply packet_disjoint_target_subrange;eauto.
   + destruct(program_bytes_leaf_subobject _ _ _ _ _ Hleaf Hpath) as [Haway|[relative [Hrelative Heq]]].
     * left;unfold packet_interval_disjoint;intuition lia.
     * right;exists relative;split;[exact Hrelative|]. split;[exact Hb|lia].
 - intros view Hview;eapply packet_disjoint_target_subrange;[apply Hpayload;exact Hview|exact Hd|exact Hinside].
Qed.

Theorem copied_declared_packet_parent_region : forall p parent root delta packets m final src source dst bytes,
 object_path p.(prog_comp_env) parent delta root -> sizeof_type p.(prog_comp_env) parent<=Ptrofs.max_unsigned ->
 0<=source ->source+sizeof_type p.(prog_comp_env) root<=Ptrofs.modulus ->
 packet_state_valid m packets -> packet_object_region_coherent p.(prog_comp_env) m packets dst 0 parent ->
 (forall shift,object_path p.(prog_comp_env) root shift Bytes ->packets src(Ptrofs.repr(source+shift))) ->
 (forall shift,object_path p.(prog_comp_env) root shift Bytes ->(align_chunk Mptr|delta+shift)) ->
 packet_copy_replacement_plan m packets src source dst delta(sizeof_type p.(prog_comp_env) root) ->
 Mem.loadbytes m src source(sizeof_type p.(prog_comp_env) root)=Some bytes ->
 Mem.storebytes m dst delta bytes=Some final ->
 packet_object_region_coherent p.(prog_comp_env) final
 (slot_copy_packets p.(prog_comp_env) packets root dst delta) dst 0 parent.
Proof.
 intros * Hfield Hbound Hsource HsourceEnd Hvalid Hparent Hcoverage Halign Hplan Hread Hstore b ofs Hin.
 pose proof(object_path_bounds _ _ _ _ Hfield) as [Hd [Hr Hinside]]. split.
 - destruct Hin as [Hold|[Hb [shift [Hpath Ho]]]].
   + exact(proj1(Hparent _ _ Hold)).
   + subst b ofs. right;exists(delta+shift). split;[eapply object_path_compose;eauto|].
     split;[reflexivity|]. pose proof(object_path_bounds _ _ _ _ Hpath) as [Hs [Hb Hl]].
     change(shift+packet_descriptor_size<=sizeof_type p.(prog_comp_env) root) in Hl.
     pose proof packet_descriptor_size_positive;rewrite Ptrofs.unsigned_repr;lia.
 - intros view Hview.
   destruct(replacement_slot_view_origin p.(prog_comp_env) root packets m final src source dst delta bytes
   Hr Hsource HsourceEnd Hd ltac:(unfold Ptrofs.max_unsigned in Hbound;lia) Hvalid Hcoverage Halign Hplan Hread Hstore
   b ofs view Hin Hview) as [old [old_offset [Hold Hbefore]]].
   exact(proj2(Hparent _ _ Hold) view Hbefore).
Qed.

Theorem declared_scalar_packet_separation : forall p m packets dst parent delta ty chunk,
 packet_object_region_coherent p.(prog_comp_env) m packets dst 0 parent ->
 scalar_object_leaf p.(prog_comp_env) parent delta ty chunk ->
 packet_write_separated m packets dst delta(size_chunk(transl_bchunk_cchunk chunk)).
Proof.
 intros * Hparent Hleaf descriptor offset Hin.
 destruct(Hparent _ _ Hin) as [Hdescriptor Hpayload].
 pose proof(scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Hs Hinside]].
 split.
 - destruct Hdescriptor as [Haway|[leaf [Hpath [Hb Ho]]]].
   + replace delta with(0+delta) by lia;eapply packet_disjoint_target_subrange;eauto.
   + destruct(program_scalar_leaf_subobject _ _ _ _ _ _ _ Hleaf Hpath) as [Haway|[relative [[Hbad Hmode] Heq]]].
     * unfold packet_interval_disjoint;right;right;destruct Haway;[right|left];change(sizeof_type p.(prog_comp_env) Bytes) with packet_descriptor_size in *;lia.
     * pose proof(object_path_descent _ _ _ _ Hbad) as Hdescent.
       destruct(bytes_object_descent_identity _ _ _ _ Hdescent) as [Ho' Ht];subst ty;discriminate Hmode.
 - intros view Hview. replace delta with(0+delta) by lia.
   eapply packet_disjoint_target_subrange;[apply Hpayload;exact Hview|exact Hd|exact Hinside].
Qed.

Theorem scalar_store_packet_parent_region : forall env m final packets dst parent delta chunk value,
 packet_state_valid m packets -> packet_object_region_coherent env m packets dst 0 parent ->
 packet_write_separated m packets dst delta(size_chunk chunk) ->
 Mem.store chunk m dst delta value=Some final ->
 packet_object_region_coherent env final packets dst 0 parent.
Proof.
 intros * Hvalid Hparent Hseparated Hstore descriptor offset Hin;split;[exact(proj1(Hparent _ _ Hin))|].
 intros view Hview. assert(Hbefore:packet_descriptor_valid m descriptor offset view).
 { eapply preserved_packet_view_origin;[exact Hvalid| |exact Hin|exact Hview].
 intros b ofs Hpacket v Hv;eapply packet_descriptor_store_frame;[exact Hstore|exact(proj1(Hseparated _ _ Hpacket))|exact Hv]. }
 exact(proj2(Hparent _ _ Hin) view Hbefore).
Qed.
