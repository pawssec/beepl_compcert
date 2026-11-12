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

Theorem initialize_scalar_array_heap : forall ge p Gamma Sigma vm m objects cells packets arr elem attr values chunk,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma vm m objects cells packets -> coherent_layout cells ->
  Forall(fun v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v elem) nil elem /\
    value_locations(packet_heap_locations ge cells objects packets) v elem) values ->
  access_mode_type elem=By_value(transl_bchunk_cchunk chunk) ->
  storage_type_check ge.(genv_cenv)(Atype elem(Z.of_nat(length values)) attr)=true ->
  exists final fresh cells',
    sem_array_init ge Sigma arr(Atype elem(Z.of_nat(length values)) attr) values vm m
      (PTree.set arr(fresh,Atype elem(Z.of_nat(length values)) attr) vm) final
      (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh(Atype elem(Z.of_nat(length values)) attr) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero(Atype elem(Z.of_nat(length values)) attr)) cells' packets /\
    coherent_layout cells'.
Proof.
  intros ge p Gamma Sigma vm m objects cells packets arr elem attr values chunk Henv Hheap Hcoherent Hvalues Hmode Hstorage.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  set(array:=Atype elem(Z.of_nat(length values)) attr).
  destruct(Mem.alloc m 0(sizeof_type ge.(genv_cenv) array)) as [allocated fresh] eqn:Halloc.
  pose proof(Mem.fresh_block_alloc _ _ _ _ _ Halloc) as Hfresh.
  pose proof(storage_type_size_bounds _ _ Hstorage) as HsizeArray;fold array in HsizeArray.
  pose proof(array_storage_element_nonvolatile _ _ _ _ Hstorage) as Hnonvolatile.
  destruct(scalar_array_stride ge.(genv_cenv) elem chunk Hmode) as [Hwidth [Hpositive Hstride]].
  assert(HarraySize:sizeof_type ge.(genv_cenv) array=Z.of_nat(length values)*sizeof_type ge.(genv_cenv) elem).
  { unfold array;simpl;rewrite Z.max_r by lia;ring. }
  assert(HscalarValues:array_scalar_values ge.(genv_cenv) Gamma Sigma(descriptor_heap_locations ge cells objects) elem values).
  { eapply Forall_impl;[|exact Hvalues]. intros v [Ht Hl];split;[exact Ht|].
    eapply packet_value_locations_nonbytes;[intro Heq;subst elem;discriminate Hmode|exact Hl]. }
  assert(HcellsAllocated:typed_memory_layout ge.(genv_cenv) Sigma cells allocated).
  { intros b ofs ty ch Hin;eapply typed_memory_cell_alloc_frame;
      [exact Halloc|exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)]. }
  assert(HlocationsAllocated:memory_locations(descriptor_heap_locations ge cells objects) cells allocated).
  { eapply allocation_memory_locations;
      [exact(initialized_object_cells _ _ _ _ _ Hmemory)|exact(initialized_object_locations _ _ _ _ _ Hmemory)|exact Halloc]. }
  pose proof(packet_heap_allocation_frame _ _ _ _ _ _ _ _ _ Hpacket Halloc) as HpacketAllocated.
  pose proof(allocated_packet_block_disjoint _ _ _ _ _ _ (packet_heap_valid _ _ _ _ _ _ Hpacket) Halloc) as HpacketApart.
  assert(HcellApart:forall b ofs ty ch,cells b ofs ty ch ->b<>fresh).
  { intros b ofs ty ch Hin Heq;subst b;apply Hfresh.
    eapply initialized_scalar_valid_block;eapply typed_memory_cell_erasure;
      exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin). }
  destruct(initialize_scalar_array_elements ge ge.(genv_cenv) Gamma Sigma(descriptor_heap_locations ge cells objects)
    elem chunk values allocated fresh Ptrofs.zero cells packets HscalarValues Hmode Hnonvolatile eq_refl
    HcellsAllocated HlocationsAllocated Hcoherent(packet_heap_valid _ _ _ _ _ _ HpacketAllocated) HpacketApart)
    as [final [after [Hhelper [Htyped [Hlocated [Hcoherent' [Hvalid [HpacketApart' [Hinc [Hcoverage Hprovenance]]]]]]]]]].
  - rewrite Ptrofs.unsigned_zero,Z.add_0_l,<-HarraySize.
    intros position Hin;eapply Mem.perm_alloc_2;[exact Halloc|exact Hin].
  - rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r.
  - rewrite Ptrofs.unsigned_zero,Z.add_0_l,<-HarraySize;exact(proj2 HsizeArray).
  - intros b ofs ty ch Hin;left;eapply HcellApart;exact Hin.
  - assert(HoriginCells:forall b ofs ty ch,after b ofs ty ch ->cells b ofs ty ch \/ b=fresh).
    { intros b ofs ty ch Hin;destruct(Hprovenance _ _ _ _ Hin) as [Hold|[i [Hi [Hb Hrest]]]];[left;exact Hold|right;exact Hb]. }
    assert(Hinit:sem_array_init ge Sigma arr array values vm m(PTree.set arr(fresh,array) vm) final(PTree.set fresh array Sigma)).
    { eapply sem_allocate_array with(loc:=fresh)(m':=allocated)(aty:=elem)(len:=Z.of_nat(length values))(a:=attr).
      - eapply alloc_variables_con;[unfold balloc;rewrite Halloc;reflexivity|constructor].
      - apply PTree.gss.
      - reflexivity.
      - reflexivity.
      - exact Hhelper. }
    destruct(array_initialization_store_typing ge ge.(genv_cenv) Gamma Sigma arr elem(Z.of_nat(length values)) attr values vm m
      (PTree.set arr(fresh,array) vm) final(PTree.set fresh array Sigma) Hinit Hblocks(proj1 HsizeArray))
      as [actual [Hlookup [Hext [Hblocks' Hvalue]]]].
    rewrite PTree.gss in Hlookup;inversion Hlookup;subst actual.
    assert(Hroot:object_type_at ge.(genv_cenv)(PTree.set fresh array Sigma) fresh 0 array).
    { inversion Hvalue;subst;rewrite Ptrofs.unsigned_zero in *;assumption. }
    assert(Hindexed:array_reference_locations ge.(genv_cenv) after fresh Ptrofs.zero array).
    { exists elem,(Z.of_nat(length values)),attr;split;[reflexivity|]. split;[lia|].
      intros i Hi;rewrite Nat2Z.id in Hi;exists chunk.
      rewrite Ptrofs.add_zero_l. rewrite Ptrofs.unsigned_zero in Hcoverage;rewrite ?Z.add_0_l in Hcoverage;apply Hcoverage;exact Hi. }
    assert(HobjectApart:forall b base ty,objects b base ty ->b<>fresh).
    { intros b base ty Hin Heq;subst b;apply Hfresh.
      destruct(aggregate_object_readable _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hin)
        as [_ [_ [_ [Hb Hr]]]];exact Hb. }
    assert(Hregions:forall delta child,object_path ge.(genv_cenv) array delta child ->
      scalar_object_region_coherent ge.(genv_cenv) after fresh delta child).
    { intros delta child Hpath;destruct(Nat.eq_dec(length values) 0) as [Hzero|Hnonzero].
      - intros b ofs ty ch Hin;destruct(Hprovenance _ _ _ _ Hin) as [Hold|[i [Hi Hrest]]].
        + left;left;eapply HcellApart;exact Hold.
        + lia.
      - replace delta with(0+delta) by lia;rewrite <-Ptrofs.unsigned_zero.
        rewrite Henv in Hindexed,Htyped,Hpath,HarraySize,HsizeArray,Hpositive |- *.
        eapply (callable_scalar_array_regions p Sigma final after fresh Ptrofs.zero elem (Z.of_nat(length values)) attr);
          [exact Htyped|exact Hcoherent'|exact Hindexed| | |exact Hpath].
        + fold array;rewrite HarraySize;nia.
        + fold array;rewrite Ptrofs.unsigned_zero;lia. }
    assert(HfinalPacket:packet_heap_invariant ge(PTree.set fresh array Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero array) after packets).
    { eapply packet_heap_fresh_array_elements;
        [exact Hpacket|exact Hext|exact Halloc|exact Hhelper| |exact HoriginCells].
      intros delta Hpath;unfold bytes_object_leaf in Hpath.
      destruct(by_value_array_object_paths _ _ _ _ _ _ _ Hmode Hpath) as [[Hd Hty]|[i [Hi [Hd Hty]]]];
        [discriminate|subst elem;discriminate Hmode]. }
    assert(HfinalMemory:initialized_object_memory ge(PTree.set fresh array Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero array) after).
    { constructor.
      - pose proof(array_initialization_preserves_descriptors _ _ _ _ _ _ _ _ _ _ _ _ Hinit
          (initialized_object_descriptors _ _ _ _ _ Hmemory) Hext) as Hold.
        constructor;intros b base ty [Hin|[Hb [Hbase Hty]]].
        + eapply aggregate_object_typing;eauto.
        + subst;rewrite Ptrofs.unsigned_zero;exact Hroot.
        + eapply aggregate_object_readable;eauto.
        + subst. destruct(allocated_array_helper_full_range _ _ _ _ _ _ _ _ Halloc Hhelper) as [Hb Hr].
          unfold aggregate_readable;rewrite Ptrofs.unsigned_zero;split;[reflexivity|]. split;[exact(proj1 HsizeArray)|].
          split;[unfold Ptrofs.max_unsigned in HsizeArray;lia|]. split;[exact Hb|].
          intros pos Hin;eapply Mem.perm_implies;[apply Hr;lia|constructor].
        + eapply aggregate_object_address_bound;eauto.
        + subst;rewrite Ptrofs.unsigned_zero;lia.
      - intros b base ty [Hin|[Hb [Hbase Hty]]] delta t ch Hleaf.
        + destruct(initialized_object_leaves _ _ _ _ _ Hmemory _ _ _ Hin _ _ _ Hleaf) as [stored [Hcell Heq]].
          exists stored;split;[apply Hinc;exact Hcell|exact Heq].
        + subst;eapply callable_scalar_array_coverage;
            [exact Htyped|exact Hindexed|fold array;rewrite Ptrofs.unsigned_zero;lia|exact Hleaf].
      - eapply typed_memory_layout_context_extension;eauto.
      - intros b ofs ty ch Hin v Hread;eapply value_locations_monotone;[|eapply Hlocated;eauto].
        eapply descriptor_heap_locations_monotone;[exact Hinc|intros;left;assumption].
      - intros b base root [Hold|[Hb [Hbase Hty]]] delta child Hpath.
        + intros cell ofs ty ch Hin;destruct(HoriginCells _ _ _ _ Hin) as [Hbefore|HfreshCell].
          * eapply initialized_object_scalar_coherence;eauto.
          * left;left;subst cell;intro Heq;symmetry in Heq;eapply HobjectApart;eauto.
        + subst;rewrite Ptrofs.unsigned_zero,Z.add_0_l;apply Hregions;exact Hpath. }
    assert(HfinalExtents:heap_block_extents(PTree.set fresh array Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero array) after packets).
    { eapply heap_extents_array_helper;[|exact Hhelper].
      eapply heap_extents_allocation;[exact Hextents|exact Halloc|exact HsizeArray|].
      eapply tracked_data_block_same_block_extension.
      - intros;eapply store_set_lookup_origin;eauto.
      - intros b base root [Hold|[Hb Hrest]];[left;exact Hold|right;exact Hb].
      - exact HoriginCells.
      - intros;left;assumption. }
    exists final,fresh,after;split;[exact Hinit|]. split;[|exact Hcoherent'].
    constructor;try assumption;intros;try(left;assumption);assumption.
Qed.
