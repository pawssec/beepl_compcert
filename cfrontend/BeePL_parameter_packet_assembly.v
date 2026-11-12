(* Packet-invariant assembly for an independently preallocated object slot.
   The actual copy supplies coverage and view provenance; no aliases are guessed. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory BeePL_scalar_object_layout.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_heap BeePL_packet_coverage.
Require Import BeePL_packet_object_layout BeePL_packet_mutation.
Require Import BeePL_object_separation BeePL_array_copy_sources BeePL_copy_array_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Lemma program_bytes_leaf_subobject : forall p root leaf_offset child_offset child,
  object_path p.(prog_comp_env) root leaf_offset Bytes ->
  object_path p.(prog_comp_env) root child_offset child ->
  (leaf_offset+packet_descriptor_size<=child_offset \/
    child_offset+sizeof_type p.(prog_comp_env) child<=leaf_offset) \/
  exists relative,object_path p.(prog_comp_env) child relative Bytes /\ leaf_offset=child_offset+relative.
Proof.
  intros p root leaf_offset child_offset child Hleaf Hchild.
  destruct(program_object_descents_separate_or_nested _ _ _ _ _ _ _
    (object_path_descent _ _ _ _ Hleaf)(object_path_descent _ _ _ _ Hchild))
    as [Hbefore|[Hafter|[Hdown|Hup]]].
  - left;left;exact Hbefore.
  - left;right;exact Hafter.
  - destruct(bytes_object_path_identity _ _ _(object_descent_as_path _ _ _ _ _ Hdown)) as [Hoffset Htype].
    subst child. right;exists 0;split;[apply path_root;change(0<=packet_descriptor_size);pose proof packet_descriptor_size_positive;lia|lia].
  - right;exists(leaf_offset-child_offset);split;[eapply object_descent_as_path;exact Hup|lia].
Qed.

Require Import BeePL_packet_copy.
Theorem assemble_preallocated_object_packet_heap :
  forall ge p Sigma larger m final objects cells packets rootType dst after,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  packet_heap_invariant ge Sigma m objects cells packets -> store_context_extends Sigma larger ->
  (forall b base ty,objects b base ty -> b<>dst) ->
  packet_block_disjoint m packets dst ->
  (forall b ofs ty chunk,after b ofs ty chunk -> cells b ofs ty chunk \/ b=dst) ->
  (forall delta child,object_path ge.(genv_cenv)rootType delta child ->
    scalar_object_region_coherent ge.(genv_cenv) after dst delta child) ->
  object_type_at ge.(genv_cenv) larger dst 0 rootType ->
  sizeof_type ge.(genv_cenv) rootType<=Ptrofs.modulus ->
  packet_state_valid final(copied_object_packets ge.(genv_cenv) packets rootType dst) ->
  (forall b ofs view,copied_object_packets ge.(genv_cenv) packets rootType dst b ofs ->
    packet_descriptor_valid final b ofs view ->
    exists old oldofs,packets old oldofs /\ packet_descriptor_valid m old oldofs view) ->
  packet_heap_invariant ge larger final
    (add_aggregate_descriptor objects dst Ptrofs.zero rootType) after
    (copied_object_packets ge.(genv_cenv) packets rootType dst).
Proof.
  intros ge p Sigma larger m final objects cells packets rootType dst after Henv Hheap Hext HobjectApart
    HpacketApart Hcells Hregions Hroot Hend Hvalid Horigin.
  assert(Hrepr:forall delta,object_path ge.(genv_cenv) rootType delta Bytes ->
    Ptrofs.unsigned(Ptrofs.repr delta)=delta).
  { intros delta Hpath. apply Ptrofs.unsigned_repr.
    exact(proj1(bytes_path_relative_bound _ _ _ Hend Hpath)). }
  constructor.
  - exact Hvalid.
  - eapply copied_object_packets_typed;[exact Hext| |exact Hend|exact Hroot].
    eapply packet_heap_typed;eauto.
  - eapply copied_object_packets_coverage;eapply packet_heap_coverage;eauto.
  - intros b ofs ty chunk Hcell descriptor offset Hpacket. split.
    + destruct Hpacket as [Hold|[Hd [delta [Hpath Ho]]]].
      * destruct(Hcells _ _ _ _ Hcell) as [HoldCell|Hb].
        -- exact(proj1(packet_heap_separation _ _ _ _ _ _ Hheap _ _ _ _ HoldCell _ _ Hold)).
        -- subst b. right;left;exact(proj1(HpacketApart _ _ Hold)).
      * subst descriptor offset. pose proof(Hregions _ _ Hpath _ _ _ _ Hcell) as Hregion.
        destruct Hregion as [[Hneq|[Hbefore|Hafter]]|[relative [[Hbad Hmode] Hrest]]].
        -- right;left;congruence.
        -- right;right;right;rewrite ?Z.add_0_l;rewrite Hrepr by assumption;exact Hbefore.
        -- right;right;left;rewrite ?Z.add_0_l;rewrite Hrepr by assumption;exact Hafter.
        -- destruct(bytes_object_path_identity _ _ _ Hbad) as [Hr Hty];subst ty;simpl in Hmode;discriminate.
    + intros view Hview. destruct(Horigin _ _ _ Hpacket Hview) as [old [oldofs [Hold Hbefore]]].
      destruct(Hcells _ _ _ _ Hcell) as [HoldCell|Hb].
      * exact(proj2(packet_heap_separation _ _ _ _ _ _ Hheap _ _ _ _ HoldCell _ _ Hold) _ Hbefore).
      * subst b;right;left;exact(proj2(HpacketApart _ _ Hold) _ Hbefore).
  - intros b base root Hobject delta child Hpath descriptor offset Hpacket. split.
    + destruct Hobject as [HoldObject|[Hb [Hbase HrootTy]]];destruct Hpacket as [HoldPacket|[Hd [leaf [Hleaf Ho]]]].
      * exact(proj1(packet_heap_object_coherence _ _ _ _ _ _ Hheap _ _ _ HoldObject _ _ Hpath _ _ HoldPacket)).
      * subst descriptor. left;right;left;intro Heq;symmetry in Heq;eapply HobjectApart;eauto.
      * subst b. left;right;left;exact(proj1(HpacketApart _ _ HoldPacket)).
      * subst b base root descriptor offset. rewrite Ptrofs.unsigned_zero,Z.add_0_l.
        pose proof Hleaf as Hfull.
        rewrite Henv in Hfull,Hpath.
        destruct(program_bytes_leaf_subobject _ _ _ _ _ Hfull Hpath) as [[Hbefore|Hafter]|[relative [Hrelative Hposition]]].
        -- left;right;right;left;rewrite ?Z.add_0_l;rewrite Hrepr by assumption;try rewrite <-Henv in Hbefore;exact Hbefore.
        -- left;right;right;right;rewrite ?Z.add_0_l;rewrite Hrepr by assumption;try rewrite <-Henv in Hafter;exact Hafter.
        -- right;exists relative;split;[rewrite Henv;exact Hrelative|]. split;[reflexivity|].
           rewrite ?Z.add_0_l;rewrite Hrepr by assumption;try rewrite <-Henv in Hposition;exact Hposition.
    + intros view Hview. destruct(Horigin _ _ _ Hpacket Hview) as [old [oldofs [Hold Hbefore]]].
      destruct Hobject as [HoldObject|[Hb Hrest]].
      * exact(proj2(packet_heap_object_coherence _ _ _ _ _ _ Hheap _ _ _ HoldObject _ _ Hpath _ _ Hold) _ Hbefore).
      * subst b;right;left;exact(proj2(HpacketApart _ _ Hold) _ Hbefore).
Qed.
