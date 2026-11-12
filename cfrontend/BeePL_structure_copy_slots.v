(* Copy into a declared field may replace an earlier initialization of that
   same field. Target region evidence admits exact aliases, not only gaps. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_object_paths.
Require Import BeePL_scalar_object_layout BeePL_scalar_object_coherence BeePL_copy_cells.
Require Import BeePL_initializer_slot BeePL_packet_replacement BeePL_packet_object_layout.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_coverage BeePL_bytes_execution.
Local Open Scope Z_scope.

Theorem declared_field_copy_layout_plan : forall env Sigma m cells src source dst target root,
 typed_memory_layout env Sigma cells m ->
 0<=source -> source+sizeof_type env root<=Ptrofs.modulus ->
 0<=target -> target+sizeof_type env root<=Ptrofs.modulus ->
 scalar_object_region_coherent env cells dst target root ->
 (forall delta ty chunk,scalar_object_leaf env root delta ty chunk ->
 exists stored,cells src(Ptrofs.repr(source+delta)) ty stored /\ transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) ->
 slot_copy_alignment cells src source target(sizeof_type env root) ->
 scalar_copy_plan cells(slot_copy_layout cells src source dst target(sizeof_type env root))
 src source dst target(sizeof_type env root).
Proof.
 intros * Htyped Hsource HsourceBound Htarget HtargetBound Hregion Hcoverage Halign
 b ofs ty chunk [Hold|[Hb [old [delta [Hcell [Hoffset [Hd [Hinside Heq]]]]]]]].
 - destruct(Hregion _ _ _ _ Hold) as [Haway|[delta [Hleaf [Hb Ho]]]].
   + left;split;assumption.
   + right;split;[exact Hb|]. exists delta,(Ptrofs.repr(source+delta)).
     destruct(Hcoverage _ _ _ Hleaf) as [stored [HsourceCell Hchunk]].
     assert(stored=chunk) by(apply source_chunk_translation_injective;exact Hchunk);subst stored.
     pose proof(scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hd [Hs Hinside]].
     pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
     split;[exact HsourceCell|]. split;[exact Hd|]. split;[exact Hinside|].
     split;[apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia|]. split;[exact Ho|].
     exact(proj2(typed_cell_permission _ _ _ _ _ _ _(Htyped _ _ _ _ Hold))).
 - subst b ofs. right;split;[reflexivity|]. exists delta,old.
   pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
   assert(Hrepr:Ptrofs.unsigned(Ptrofs.repr(target+delta))=target+delta) by(apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia).
   repeat split;try assumption;rewrite Hrepr;eauto.
Qed.

Theorem declared_field_packet_replacement_plan : forall env m packets src source dst target root,
 0<=source -> source+sizeof_type env root<=Ptrofs.modulus ->
 packet_state_valid m packets -> packet_object_region_coherent env m packets dst target root ->
 (forall delta,object_path env root delta Bytes ->packets src(Ptrofs.repr(source+delta))) ->
 packet_copy_replacement_plan m packets src source dst target(sizeof_type env root).
Proof.
 intros * Hsource Hbound Hvalid Hregion Hcoverage. split.
 - intros descriptor offset Hin. destruct(proj1(Hregion _ _ Hin)) as [Haway|[delta [Hpath [Hb Ho]]]].
   + left;exact Haway.
   + right;exists delta,(Ptrofs.repr(source+delta)).
     pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [Hs Hinside]].
     change(delta+packet_descriptor_size<=sizeof_type env root) in Hinside.
     pose proof packet_descriptor_size_positive.
     split;[exact Hb|]. split;[exact Ho|]. split;[apply Hcoverage;exact Hpath|].
     split;[apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia|]. split;[exact Hd|]. split;[exact Hinside|].
     destruct(Hvalid _ _ Hin) as [_ [view [bytes [Hdescriptor Hcontents]]]].
     rewrite <-Ho;eapply packet_descriptor_alignment;exact Hdescriptor.
 - intros descriptor offset Hin view Hview;exact(proj2(Hregion _ _ Hin) _ Hview).
Qed.
