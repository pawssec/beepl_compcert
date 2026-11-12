(* A completed aggregate/Bytes parameter binding uses the same real copy
   operation as a one-element initializer, into its independently allocated
   parameter block. All premises describe the pre-state. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations BeePL_layout_coherence.
Require Import BeePL_object_paths BeePL_packet_state BeePL_packet_heap BeePL_block_extents.
Require Import BeePL_general_array_initialization BeePL_copy_array_initialization.
Require Import BeePL_copy_array_coverage BeePL_array_proofs BeePL_initializer_slot.
Import ListNotations.
Local Open Scope Z_scope.

Theorem bind_copy_parameter_slot : forall ge p Sigma L vm m cells packets id root v dst,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  is_aggregate_type root=true \/ root=Bytes ->
  vm ! id=Some(dst,root) ->
  source_block_extent m dst (sizeof_type ge.(genv_cenv) root) ->
  array_copy_source ge.(genv_cenv) cells packets m dst root v ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets ->
  (forall b ofs ty chunk,cells b ofs ty chunk -> b<>dst) ->
  packet_block_disjoint m packets dst ->
  exists final after after_packets,
    bind_variables ge vm m [(id,root)] [v] final /\
    sem_array_init_helper ge m dst Ptrofs.zero [v] root final /\
    typed_memory_layout ge.(genv_cenv) Sigma after final /\ memory_locations L after final /\
    coherent_layout after /\ packet_state_valid final after_packets /\
    (forall b ofs ty chunk,cells b ofs ty chunk -> after b ofs ty chunk) /\
    (forall b ofs,packets b ofs -> after_packets b ofs) /\
    (forall delta ty chunk,scalar_object_leaf ge.(genv_cenv) root delta ty chunk ->
      exists stored,after dst(Ptrofs.repr delta) ty stored /\
        transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) /\
    (forall delta,object_path ge.(genv_cenv) root delta Bytes ->after_packets dst(Ptrofs.repr delta)) /\
    (forall b ofs ty chunk,after b ofs ty chunk -> cells b ofs ty chunk \/ b=dst).
Proof.
  intros ge p Sigma L vm m cells packets id root v dst Henv Hkind Hget Hextent Hsource
    Htyped Hlocated Hcoherent Hpackets HcellsApart HpacketsApart.
  pose proof(source_extent_bound _ _ _ Hextent) as Hsize.
  assert(Hsources:Forall(array_copy_source ge.(genv_cenv) cells packets m dst root)[v]) by auto.
  assert(Hprefix:array_cells_prefix cells dst(Ptrofs.unsigned Ptrofs.zero)).
  { intros;left;eapply HcellsApart;eauto. }
  assert(HpacketPrefix:array_packet_prefix m packets dst(Ptrofs.unsigned Ptrofs.zero)).
  { intros b ofs Hin. destruct(HpacketsApart _ _ Hin) as [Hb Hv];split;[left;exact Hb|exact Hv]. }
  destruct(initialize_copy_array_elements ge p Sigma L root [v] cells packets m dst Ptrofs.zero cells packets
    Henv Hkind (proj1 Hsize) Hsources Htyped Hlocated Hcoherent Hpackets Hprefix HpacketPrefix)
    as [final [after [afterPackets [Hhelper [Htyped' [Hlocated' [Hcoherent' [Hvalid
      [Hprefix' [HpacketPrefix' [Hinc [Hpinc [Horigin [Hcoverage [Hbytes Hprovenance]]]]]]]]]]]]]]].
  - auto.
  - intros;left;assumption.
  - auto.
  - exact(source_extent_valid _ _ _ Hextent).
  - rewrite Ptrofs.unsigned_zero. change(Mem.range_perm m dst 0(0+1*sizeof_type ge.(genv_cenv) root) Cur Freeable).
    rewrite Z.add_0_l,Z.mul_1_l;exact(source_extent_freeable _ _ _ Hextent).
  - rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r.
  - rewrite Ptrofs.unsigned_zero. change(0+1*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned). lia.
  - rewrite Ptrofs.unsigned_zero,Henv;apply program_fresh_array_leaf_alignment;rewrite <-Henv;exact(proj1 Hsize).
  - exists final,after,afterPackets. split.
    + eapply bind_variables_cons;[exact Hget| |constructor].
      apply singleton_array_initialization;[exact Hhelper|].
      intros Heq;subst root;destruct Hkind;discriminate.
    + split;[exact Hhelper|]. split;[exact Htyped'|]. split;[exact Hlocated'|].
      split;[exact Hcoherent'|]. split;[exact Hvalid|]. split;[exact Hinc|]. split;[exact Hpinc|].
      split.
      * intros delta ty chunk Hleaf. specialize(Hcoverage 0%nat delta ty chunk ltac:(simpl;lia) Hleaf).
        rewrite Ptrofs.unsigned_zero in Hcoverage. simpl in Hcoverage;exact Hcoverage.
      * split;[|exact Horigin]. intros delta Hpath. specialize(Hbytes 0%nat delta ltac:(simpl;lia) Hpath).
        rewrite Ptrofs.unsigned_zero in Hbytes. simpl in Hbytes;exact Hbytes.
Qed.

Require Import BeePL_copy_array_views BeePL_initializer_frames BeePL_structure_proofs.

(* Canonical descriptors make the provenance needed by the next parameter
   explicit: copied payload endpoints always come from an old descriptor. *)
Lemma copied_parameter_pending_packet_block : forall ge cells packets m written root v final pending,
  sem_array_init_helper ge m written Ptrofs.zero [v] root final ->
  is_aggregate_type root=true \/ root=Bytes ->
  0<=sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned ->
  array_copy_source ge.(genv_cenv) cells packets m written root v ->
  array_copy_leaf_alignment ge.(genv_cenv) root 0 1 ->
  packet_state_valid m packets -> packet_block_disjoint m packets written ->
  packet_block_disjoint m packets pending -> written<>pending ->
  packet_block_disjoint final
    (copied_array_packets ge.(genv_cenv) packets [v] root written 0) pending.
Proof.
  intros ge cells packets m written root v final pending Hhelper Hkind Hsize Hsource Halign
    Hvalid Hwritten Hpending Hneq b ofs Hin.
  split.
  - destruct Hin as [Hold|[index [delta [Hi [Hpath [Hb Hofs]]]]]].
    + exact(proj1(Hpending _ _ Hold)).
    + subst;exact Hneq.
  - intros view Hview.
    assert(Hprefix:array_packet_prefix m packets written(Ptrofs.unsigned Ptrofs.zero)).
    { intros old offset Hold. destruct(Hwritten _ _ Hold) as [Hb Hv];split;[left;exact Hb|exact Hv]. }
    assert(Hbound:Ptrofs.unsigned Ptrofs.zero+Z.of_nat(length [v])*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned).
    { rewrite Ptrofs.unsigned_zero. change(0+1*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned);lia. }
    rewrite <- Ptrofs.unsigned_zero in Halign,Hin.
    destruct(copy_array_packet_view_origins ge cells packets packets root [v] m written Ptrofs.zero final
      Hhelper Hkind (proj1 Hsize) ltac:(auto) Hbound Halign Hvalid Hprefix ltac:(auto)
      b ofs view Hin Hview) as [old [offset [Hold Hbefore]]].
    exact(proj2(Hpending _ _ Hold) _ Hbefore).
Qed.

Lemma copy_parameter_pending_cell_block : forall (old after:scalar_layout) written pending,
  (forall b ofs ty chunk,after b ofs ty chunk -> old b ofs ty chunk \/ b=written) ->
  (forall b ofs ty chunk,old b ofs ty chunk -> b<>pending) -> written<>pending ->
  forall b ofs ty chunk,after b ofs ty chunk -> b<>pending.
Proof. intros old after written pending Horigin Hapart Hneq b ofs ty chunk Hin.
  destruct(Horigin _ _ _ _ Hin);[eapply Hapart;eauto|congruence]. Qed.

Print Assumptions bind_copy_parameter_slot.
Print Assumptions copied_parameter_pending_packet_block.

Lemma copy_parameter_remaining_source : forall ge env old after old_packets after_packets m final
    written written_type written_offset assigned result pending root v,
  array_copy_source env old old_packets m pending root v ->
  (forall source offset,v=Vloc source offset -> source<>written) ->
  assign_addr ge written_type m written written_offset Full assigned final result ->
  (forall b ofs ty chunk,old b ofs ty chunk -> after b ofs ty chunk) ->
  (forall b ofs ty chunk,after b ofs ty chunk -> old b ofs ty chunk \/ b=written) ->
  (forall b ofs,old_packets b ofs -> after_packets b ofs) ->
  array_copy_source env after after_packets final pending root v.
Proof.
  intros ge env old after old_packets after_packets m final written written_type written_offset assigned result
    pending root v Hsource HsourceApart Hassign Hinc Horigin Hpinc.
  destruct Hsource as [source offset Hv Hneq Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
  eapply array_copy_source_intro with(src:=source)(source:=offset);try assumption.
  - eapply assignment_preserves_valid_blocks;eauto.
  - intros position Hin;eapply assignment_preserves_permissions;[exact Hassign|apply Hread;exact Hin].
  - intros delta ty chunk Hleaf. destruct(Hleaves _ _ _ Hleaf) as [stored [Hcell Hchunk]].
    exists stored;split;[apply Hinc;exact Hcell|exact Hchunk].
  - intros Hpositive delta child Hpath. eapply array_current_source_regions;
      [exact(HsourceApart source offset Hv)|exact Horigin| |exact Hpath].
    apply Hregions;exact Hpositive.
  - intros;apply Hpinc,Hpackets;assumption.
Qed.
