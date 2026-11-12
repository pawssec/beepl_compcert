(* Fresh aggregate/Bytes arrays: actual allocation and element copies establish
   the shared object, scalar, packet, and allocation-profile invariants. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory BeePL_scalar_object_layout.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_heap BeePL_packet_coverage.
Require Import BeePL_packet_object_layout BeePL_packet_mutation BeePL_packet_bindings.
Require Import BeePL_general_array_initialization BeePL_copy_array_initialization BeePL_copy_array_coverage BeePL_copy_array_views.
Require Import BeePL_array_copy_sources BeePL_array_packet_assembly.
Require Import BeePL_object_separation.
Require Import BeePL_fresh_copy BeePL_initializer_frames BeePL_array_proofs BeePL_heap_extents BeePL_storage_types.
Require Import BeePL_layout_coherence BeePL_initialized_runtime.
Import ListNotations.
Local Open Scope Z_scope.

Require Import BeePL_structure_proofs BeePL_packet_copy BeePL_parameter_packet_assembly BeePL_initializer_slot BeePL_copy_array_views.
Require Import BeePL_copy_parameter_binding BeePL_block_extents BeePL_array_packet_assembly.

Theorem initialize_preallocated_aggregate_parameter : forall ge p Gamma Sigma caller m objects cells packets
    id root v target callee,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  is_aggregate_type root=true -> Sigma ! target=Some root -> callee ! id=Some(target,root) ->
  source_block_extent m target(sizeof_type ge.(genv_cenv) root) ->
  array_copy_source ge.(genv_cenv) cells packets m target root v ->
  (forall b base ty,objects b base ty ->b<>target) ->
  (forall b ofs ty chunk,cells b ofs ty chunk ->b<>target) -> packet_block_disjoint m packets target ->
  exists final after,
    bind_variables ge callee m [(id,root)] [v] final /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final
      (add_aggregate_descriptor objects target Ptrofs.zero root) after
      (copied_object_packets ge.(genv_cenv) packets root target) /\
    coherent_layout after /\
    (forall b ofs ty chunk,after b ofs ty chunk ->cells b ofs ty chunk \/ b=target).
Proof.
  intros ge p Gamma Sigma caller m objects cells packets id root v target callee
    Henv Hheap Hcoherent Hkind Hsigma Hget Hextent Hsource HobjectsApart HcellsApart HpacketsApart.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  pose proof(source_extent_bound _ _ _ Hextent) as Hsize.
  assert(HsourceOriginal:=Hsource).
  destruct Hsource as [src source Hv Hneq Hsrc HsrcBound HsrcAlign Hread Hleaves HsourceRegions HsourcePackets].
  subst v.
  assert(Hbound:sizeof_type ge.(genv_cenv) root<=Ptrofs.modulus) by(unfold Ptrofs.max_unsigned in Hsize;lia).
  assert(Hroot:object_type_at ge.(genv_cenv) Sigma target 0 root).
  { assert(Heq:stored_object_type root=root) by(destruct root;simpl in Hkind;try discriminate;reflexivity).
    rewrite <-Heq. apply object_type_root;[exact Hsigma|rewrite Heq;exact(proj1 Hsize)]. }
  assert(Hdisjoint:slot_cells_disjoint cells target 0(sizeof_type ge.(genv_cenv) root)).
  { intros;left;eapply HcellsApart;eauto. }
  assert(HleafAlign:array_copy_leaf_alignment ge.(genv_cenv) root 0 1).
  { rewrite Henv;apply program_fresh_array_leaf_alignment;rewrite <-Henv;exact(proj1 Hsize). }
  assert(HcopyAlign:slot_copy_alignment cells src(Ptrofs.unsigned source) 0(sizeof_type ge.(genv_cenv) root)).
  { destruct(Z_lt_le_dec 0(sizeof_type ge.(genv_cenv) root)) as [Hpositive|Hzero].
    - eapply array_current_source_alignment with(seed:=cells)(dst:=target);[exact Hneq|intros;left;assumption| |].
      + replace(Ptrofs.unsigned source) with(Ptrofs.unsigned source+0) by lia.
        apply(HsourceRegions Hpositive);constructor;exact(proj1 Hsize).
      + intros delta ty chunk Hleaf. destruct(HleafAlign 0%nat ltac:(lia)) as [Hs Hp].
        specialize(Hs _ _ _ Hleaf);cbn [Z.of_nat] in Hs;rewrite Z.mul_0_l,?Z.add_0_l in Hs;exact Hs.
    - intros old ty chunk delta Hin Hoff Hd Hlimit;pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia. }
  assert(HbytesAlign:forall delta,object_path ge.(genv_cenv) root delta Bytes ->(align_chunk Mptr|0+delta)).
  { intros delta Hpath. destruct(HleafAlign 0%nat ltac:(lia)) as [Hs Hp].
    specialize(Hp _ Hpath);cbn [Z.of_nat] in Hp;rewrite Z.mul_0_l,Z.add_0_r in Hp;exact Hp. }
  assert(Hready:initializer_copy_ready ge m root src source target Ptrofs.zero).
  { constructor.
    - left;exact Hkind.
    - exact(proj1 Hsize).
    - exact Hsrc.
    - exact(source_extent_valid _ _ _ Hextent).
    - exact HsrcBound.
    - rewrite Ptrofs.unsigned_zero;lia.
    - exact HsrcAlign.
    - rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r.
    - left;exact Hneq.
    - exact Hread.
    - rewrite Ptrofs.unsigned_zero,Z.add_0_l;exact(source_extent_freeable _ _ _ Hextent). }
  destruct(initialize_copy_slot ge Sigma (descriptor_heap_locations ge cells objects) cells packets m root src source target Ptrofs.zero
    Hready (initialized_object_cells _ _ _ _ _ Hmemory) (initialized_object_locations _ _ _ _ _ Hmemory))
    as [final [bytes [Hbytes [Hstore [Hassign [Htyped [Hlocated Hvalid]]]]]]].
  - rewrite Ptrofs.unsigned_zero;exact Hdisjoint.
  - rewrite Ptrofs.unsigned_zero;exact HcopyAlign.
  - exact(packet_heap_valid _ _ _ _ _ _ Hpacket).
  - exact HsourcePackets.
  - rewrite Ptrofs.unsigned_zero;exact HbytesAlign.
  - eapply packet_block_disjoint_write;exact HpacketsApart.
  - rewrite Ptrofs.unsigned_zero in Hstore,Htyped,Hlocated,Hvalid.
    set(after:=slot_copy_layout cells src(Ptrofs.unsigned source) target 0(sizeof_type ge.(genv_cenv) root)).
    assert(Hinc:forall b ofs ty chunk,cells b ofs ty chunk ->after b ofs ty chunk) by(intros;left;assumption).
    assert(Horigin:forall b ofs ty chunk,after b ofs ty chunk ->cells b ofs ty chunk \/ b=target).
    { intros b ofs ty chunk [Hold|[Hb Hrest]];auto. }
    assert(Hregions:forall delta child,object_path ge.(genv_cenv) root delta child ->
      scalar_object_region_coherent ge.(genv_cenv) after target delta child).
    { destruct(Z_lt_le_dec 0(sizeof_type ge.(genv_cenv) root)) as [Hpositive|Hzero].
      - intros delta child Hpath;replace delta with(0+delta) by lia.
        eapply slot_copy_declared_regions;[lia|lia|exact Hdisjoint|apply HsourceRegions;exact Hpositive|exact Hpath].
      - intros delta child Hpath b ofs ty chunk [Hold|[Hb [old [shift [Hin [Hoff [Hd [Hend Heq]]]]]]]].
        + left;left;eapply HcellsApart;eauto.
        + pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia. }
    assert(Hhelper:sem_array_init_helper ge m target Ptrofs.zero [Vloc src source] root final).
    { econstructor;[exact Hassign|constructor]. }
    assert(HpacketFinal:packet_heap_invariant ge Sigma final
      (add_aggregate_descriptor objects target Ptrofs.zero root) after
      (copied_object_packets ge.(genv_cenv) packets root target)).
    { eapply assemble_preallocated_object_packet_heap;
        [exact Henv|exact Hpacket|apply store_context_extends_refl|exact HobjectsApart|exact HpacketsApart|
         exact Horigin|exact Hregions|exact Hroot|exact Hbound| |].
      - change(packet_state_valid final(slot_copy_packets ge.(genv_cenv) packets root target 0));exact Hvalid.
      - intros b ofs view Hin Hview. eapply copy_array_packet_view_origins with(seed:=cells)(seed_packets:=packets)
          (values:=[Vloc src source])(root:=root)(dst:=target)(offset:=Ptrofs.zero);
          [exact Hhelper|auto|exact(proj1 Hsize)|auto| | |exact(packet_heap_valid _ _ _ _ _ _ Hpacket)| |auto| |exact Hview].
        + rewrite Ptrofs.unsigned_zero;change(0+1*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned);lia.
        + rewrite Ptrofs.unsigned_zero;exact HleafAlign.
        + intros b0 ofs0 Hp. destruct(HpacketsApart _ _ Hp) as [Hb Hv];split;[left;exact Hb|exact Hv].
        + destruct Hin as [Hold|[Hb [delta [Hpath Hofs]]]];[left;exact Hold|].
          right;exists 0%nat,delta;split;[simpl;lia|]. split;[exact Hpath|]. split;[exact Hb|].
          rewrite Ptrofs.unsigned_zero;cbn [Z.of_nat];rewrite Z.mul_0_l,?Z.add_0_l;exact Hofs. }
    assert(HextentFinal:source_block_extent final target(sizeof_type ge.(genv_cenv) root))
      by(eapply assignment_source_extent;eauto).
    assert(HmemoryFinal:initialized_object_memory ge Sigma final
      (add_aggregate_descriptor objects target Ptrofs.zero root) after).
    { constructor.
      - constructor;intros b base ty [Hold|[Hb [Hbase Hty]]].
        + eapply aggregate_object_typing;[exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hold].
        + subst;rewrite Ptrofs.unsigned_zero;exact Hroot.
        + destruct(aggregate_object_readable _ _ _ _ (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hold)
            as [Hagg [Hsz [Hbnd [Hvb Hperm]]]].
          repeat split;try assumption.
          * eapply assignment_preserves_valid_blocks;eauto.
          * intros position Hin;eapply assignment_preserves_permissions;[exact Hassign|apply Hperm;exact Hin].
        + subst;unfold aggregate_readable;rewrite Ptrofs.unsigned_zero;split;[exact Hkind|]. split;[exact(proj1 Hsize)|].
          split;[lia|]. split;[exact(source_extent_valid _ _ _ HextentFinal)|].
          intros position Hin;eapply Mem.perm_implies;[apply(source_extent_freeable _ _ _ HextentFinal);lia|constructor].
        + eapply aggregate_object_address_bound;[exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hold].
        + subst;rewrite Ptrofs.unsigned_zero;lia.
      - intros b base ty [Hold|[Hb [Hbase Hty]]] delta t chunk Hleaf.
        + destruct(initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hold _ _ _ Hleaf) as [stored [Hcell Heq]].
          exists stored;split;[apply Hinc;exact Hcell|exact Heq].
        + subst;rewrite Ptrofs.unsigned_zero;apply slot_copy_scalar_leaf_coverage;
            [exact(proj1(Ptrofs.unsigned_range source))|exact HsrcBound|exact Hleaves|exact Hleaf].
      - exact Htyped.
      - intros b ofs ty chunk Hin val Hload;eapply value_locations_monotone;[|eapply Hlocated;eauto].
        apply descriptor_heap_locations_monotone;[exact Hinc|intros;left;assumption].
      - intros b base ty [Hold|[Hb [Hbase Hty]]] delta child Hpath.
        + intros b0 ofs t chunk Hin. destruct(Horigin _ _ _ _ Hin) as [Hbefore|Hnew].
          * eapply initialized_object_scalar_coherence;eauto.
          * left;left;subst b0;intro Heq;symmetry in Heq;eapply HobjectsApart;eauto.
        + subst;rewrite Ptrofs.unsigned_zero,Z.add_0_l;apply Hregions;exact Hpath. }
    assert(HextentsFinal:heap_block_extents Sigma final
      (add_aggregate_descriptor objects target Ptrofs.zero root) after
      (copied_object_packets ge.(genv_cenv) packets root target)).
    { eapply heap_extents_registry_frame.
      - eapply heap_extents_assignment;[exact Hextents|exact Hassign].
      - intros b [HS|[[ofs [ty [chunk Hcell]]]|[[base [ty Hobject]]|[base Hpacket0]]]].
        + left;exact HS.
        + destruct(Horigin _ _ _ _ Hcell) as [Hold|Hb];[right;left;eauto|].
          subst;left;exists root;split;[exact Hsigma|destruct root;simpl in Hkind;try discriminate;reflexivity].
        + destruct Hobject as [Hold|[Hb Hrest]];[right;right;left;eauto|].
          subst;left;exists root;split;[exact Hsigma|destruct root;simpl in Hkind;try discriminate;reflexivity].
        + destruct Hpacket0 as [Hold|[Hb Hrest]];[right;right;right;eauto|].
          subst;left;exists root;split;[exact Hsigma|destruct root;simpl in Hkind;try discriminate;reflexivity]. }
    exists final,after;split;[eapply bind_variables_cons;[exact Hget|exact Hassign|constructor]|]. split.
    + constructor;try assumption.
      * apply store_context_extends_refl.
      * intros;left;assumption.
      * intros b ty Hentry;eapply assignment_preserves_valid_blocks;[exact Hassign|exact(Hblocks b ty Hentry)].
      * intros;left;assumption.
    + split;[unfold after;eapply slot_copy_layout_coherent;[exact Hcoherent|exact Hdisjoint|lia|lia]|exact Horigin].
Qed.
