(* General data-argument preparation from the caller's actual shared heap. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_initialized_runtime BeePL_packet_bindings BeePL_packet_heap BeePL_packet_state BeePL_packet.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_layout_coherence BeePL_scalar_object_layout.
Require Import BeePL_packet_descriptor_copy BeePL_packet_mutation BeePL_heap_extents BeePL_parameter_extents BeePL_parameter_allocations BeePL_allocation_proofs.
Require Import BeePL_call_memory BeePL_initializer_frames BeePL_initialized_call_entry BeePL_general_parameter_binding.
Require Import BeePL_storage_parameter_allocations BeePL_parameter_heap_fold BeePL_parameter_storage_check.
Require Import BeePL_array_copy_sources BeePL_general_array_initialization BeePL_storage_types BeePL_block_extents.
Import ListNotations.
Local Open Scope Z_scope.

Lemma parameter_allocation_heap_evolution : forall ge Gamma Sigma caller m objects cells packets
    initial params callee allocated Sigma',
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->
  Forall(fun param=>storage_type_check ge.(genv_cenv)(snd param)=true) params ->
  alloc_variables ge Sigma initial m params callee allocated Sigma' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' allocated objects cells packets.
Proof.
  intros ge Gamma Sigma caller m objects cells packets initial params callee allocated Sigma' Hheap Hstorage Ha.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  destruct(alloc_variables_store_extension _ _ _ _ _ _ _ _ Ha Hblocks) as [Hext Hblocks'].
  destruct(parameter_allocation_packet_frame _ _ _ _ _ _ _ _ _ Ha(packet_heap_valid _ _ _ _ _ _ Hpacket)) as [Hvalid Hviews].
  assert(Hmemory':initialized_object_memory ge Sigma' allocated objects cells).
  { constructor.
    - eapply aggregate_objects_valid_frame;[exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hext| |].
      + intros;eapply parameter_allocations_block_frame;eauto.
      + intros;eapply variable_allocation_preserves_permissions;eauto.
    - exact(initialized_object_leaves _ _ _ _ _ Hmemory).
    - intros b ofs ty chunk Hin. destruct(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)
        as [Hmode Hvol Haccess [cv [v [Hload [Hdecode Htyped]]]]].
      constructor;try assumption.
      + eapply parameter_allocations_access_frame;eauto.
      + exists cv,v;split;[rewrite(parameter_allocations_load_frame _ _ _ _ _ _ _ _ Ha);[exact Hload|eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Haccess|constructor]]|].
        split;[exact Hdecode|eapply(proj2 typing_store_extension);eauto].
    - intros b ofs ty chunk Hin v Hread.
      destruct(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hin)
        as [Hmode Hvol Haccess [cv [old [Hload [Hdecode Htyped]]]]].
      assert(HreadOld:deref_addr ty m b ofs Full old) by(eapply deref_addr_value;eauto).
      assert(HreadAfter:deref_addr ty allocated b ofs Full old).
      { eapply deref_addr_value;eauto;simpl;rewrite(parameter_allocations_load_frame _ _ _ _ _ _ _ _ Ha);[exact Hload|eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Haccess|constructor]]. }
      assert(v=old) by(eapply deref_full_deterministic;eauto);subst v.
      eapply initialized_object_locations;eauto.
    - exact(initialized_object_scalar_coherence _ _ _ _ _ Hmemory). }
  assert(Hpacket':packet_heap_invariant ge Sigma' allocated objects cells packets).
  { constructor;try assumption.
    - intros b ofs Hin;eapply object_type_at_store_extension;[eapply packet_heap_typed;eauto|exact Hext].
    - exact(packet_heap_coverage _ _ _ _ _ _ Hpacket).
    - eapply packet_layout_separation_frame;[exact(packet_heap_valid _ _ _ _ _ _ Hpacket)|exact Hviews|exact(packet_heap_separation _ _ _ _ _ _ Hpacket)].
    - eapply packet_object_coherence_frames;[exact(packet_heap_valid _ _ _ _ _ _ Hpacket)|exact Hviews|exact(packet_heap_object_coherence _ _ _ _ _ _ Hpacket)]. }
  constructor;try assumption;try(intros;assumption).
  eapply storage_parameter_allocation_heap_extents;eauto.
Qed.

Theorem allocated_heap_parameter_inputs : forall ge p Gamma Sigma caller m objects cells packets
    params values initial callee allocated Sigma',
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->coherent_layout cells ->
  Forall(fun param=>storage_type_check ge.(genv_cenv)(snd param)=true) params ->NoDup(map fst params) ->
  Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
    value_locations(packet_heap_locations ge cells objects packets) v(snd param)) params values ->
  alloc_variables ge Sigma initial m params callee allocated Sigma' ->
  Forall2(heap_parameter_input ge Gamma Sigma' callee allocated objects cells packets params) params values.
Proof.
  intros ge p Gamma Sigma caller m objects cells packets params values initial callee allocated Sigma'
    Henv Hheap Hcoherent Hstorage Hnames Hvalues Ha.
  pose proof(allocated_general_parameter_inputs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hheap Hcoherent Hstorage Hnames Hvalues Ha) as Hbasic.
  destruct(parameter_allocation_slots _ _ _ _ _ _ _ _ Ha Hnames) as [Hslots Hdistinct].
  pose proof(initialized_heap_blocks _ _ _ _ _ _ _ _ Hheap) as Hblocks.
  pose proof(initialized_heap_memory _ _ _ _ _ _ _ _ Hheap) as Hmemory.
  pose proof(initialized_heap_packets _ _ _ _ _ _ _ _ Hheap) as Hpacket.
  pose proof(packet_heap_valid _ _ _ _ _ _ Hpacket) as Hvalid.
  destruct(parameter_allocation_packet_frame _ _ _ _ _ _ _ _ _ Ha Hvalid) as [HvalidAllocated Hviews].
  assert(Hall:forall id ty v,In(id,ty)params ->
    type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty ->
    value_locations(packet_heap_locations ge cells objects packets) v ty ->
    heap_parameter_input ge Gamma Sigma' callee allocated objects cells packets params (id,ty) v).
  { intros id ty v Hin Htyped Hloc. destruct(Hslots _ _ Hin) as [target [Hget [Hfresh Hrest]]].
    pose proof(allocated_parameter_store_lookup _ _ _ _ _ _ _ _ Ha Hnames Hblocks _ _ _ Hin Hget) as Hsigma.
    destruct(alloc_variables_store_extension _ _ _ _ _ _ _ _ Ha Hblocks) as [Hext Hblocks'].
    unfold heap_parameter_input;split.
    - rewrite Forall_forall in Hstorage;exact(Hstorage(id,ty) Hin).
    - split;[eapply(proj2 typing_store_extension);eauto|]. split;[exact Hloc|].
      exists target;split;[exact Hget|]. split;[exact Hsigma|]. split.
      + eapply storage_parameter_allocation_slots;eauto.
      + split.
        * intros b base root Hobj Heq;subst b;apply Hfresh.
          destruct(aggregate_object_readable _ _ _ _(initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobj)
            as [_ [_ [_ [Hb Hr]]]];exact Hb.
        * split.
          -- intros b ofs root ch Hcell Heq;subst b;apply Hfresh;eapply initialized_scalar_valid_block;
               eapply typed_memory_cell_erasure;exact(initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell).
          -- split.
             ++ intros b ofs Hp;split.
                ** intro Heq;subst b;apply Hfresh. destruct(Hvalid _ _ Hp) as [_ [view [contents [Hd Hc]]]].
                   eapply packet_descriptor_source_block;eauto.
                ** intros view Hd. pose proof(preserved_packet_view_origin _ _ _ Hvalid Hviews _ _ _ Hp Hd) as Hold.
                   intro Heq;apply Hfresh;rewrite <-Heq;exact(proj1(proj2(proj2(proj2 Hold)))).
             ++ split.
                ** intros Hkind;eapply copy_source_parameter_allocation_frame;[exact Ha|]. eapply typed_located_array_copy_source;eauto;exact(initialized_heap_extents _ _ _ _ _ _ _ _ Hheap).
                ** intros Hkind src source Hv written [name [otherType [Hmember Hlookup]]].
                   destruct(Hslots _ _ Hmember) as [actual [Hactual [HactualFresh Hrest2]]].
                   rewrite Hlookup in Hactual;inversion Hactual;subst actual.
                   assert(Hsource:array_copy_source ge.(genv_cenv) cells packets m target ty v)
                     by(eapply typed_located_array_copy_source;eauto;exact(initialized_heap_extents _ _ _ _ _ _ _ _ Hheap)).
                   destruct Hsource as [origin offset Heq Hneq Hsrc Hmore]. rewrite Hv in Heq;inversion Heq;subst origin offset.
                   intro Hsame;subst written;contradiction. }
  assert(Hmap:forall remaining vals,incl remaining params ->
    Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
      value_locations(packet_heap_locations ge cells objects packets) v(snd param)) remaining vals ->
    Forall2(heap_parameter_input ge Gamma Sigma' callee allocated objects cells packets params) remaining vals).
  { intros remaining vals Hsub Hrel. induction Hrel;constructor.
    - destruct x as [id ty];destruct H as [Ht Hl];eapply Hall;[apply Hsub;left;reflexivity|exact Ht|exact Hl].
    - apply IHHrel;intros item Hi;apply Hsub;right;exact Hi. }
  apply Hmap;[intros item Hi;exact Hi|exact Hvalues].
Qed.

Theorem general_parameter_heap_preparation : forall ge p Gamma Sigma caller m objects cells packets
    params values initial,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->coherent_layout cells ->
  Forall(fun param=>storage_type_check ge.(genv_cenv)(snd param)=true) params ->NoDup(map fst params) ->
  Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
    value_locations(packet_heap_locations ge cells objects packets) v(snd param)) params values ->
  exists callee allocated final Sigma' objects' cells' packets',
    alloc_variables ge Sigma initial m params callee allocated Sigma' /\
    bind_variables ge callee allocated params values final /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_layout cells' /\
    forall id ty,In(id,ty)params ->packet_variable_binding ge Sigma' callee cells' objects' packets' id ty.
Proof.
  intros ge p Gamma Sigma caller m objects cells packets params values initial Henv Hheap Hcoherent Hstorage Hnames Hvalues.
  destruct(data_parameter_allocation_total ge Sigma initial m params) as [callee [allocated [Sigma' Ha]]].
  pose proof(parameter_allocation_heap_evolution _ _ _ _ _ _ _ _ _ _ _ _ _ Hheap Hstorage Ha) as HallocStep.
  pose proof(allocated_heap_parameter_inputs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hheap Hcoherent Hstorage Hnames Hvalues Ha) as Hinputs.
  destruct(initialize_parameter_heap_fold ge p Gamma Sigma' caller callee params params values allocated objects cells packets
    Henv(initialized_heap_state_evolve _ _ _ _ _ _ _ _ _ _ _ _ _ Hheap HallocStep) Hcoherent
    ltac:(intros x Hx;exact Hx)(proj2(parameter_allocation_slots _ _ _ _ _ _ _ _ Ha Hnames)) Hinputs)
    as [final [objects' [cells' [packets' [Hb [HbindStep [Hcoherent' Hbindings]]]]]]].
  exists callee,allocated,final,Sigma',objects',cells',packets';split;[exact Ha|]. split;[exact Hb|]. split.
  - eapply initialized_heap_evolution_trans;[exact HallocStep|exact HbindStep].
  - auto.
Qed.

Print Assumptions general_parameter_heap_preparation.
