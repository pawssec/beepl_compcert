(* Uniform completed data-slot transition, used by the heterogeneous call fold. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_initialized_runtime BeePL_packet_bindings BeePL_packet_heap BeePL_packet_state.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_soundness_variables BeePL_callable_variables.
Require Import BeePL_layout_coherence BeePL_runtime_locations BeePL_block_extents BeePL_storage_types.
Require Import BeePL_general_parameter_binding BeePL_general_array_initialization BeePL_call_bindings.
Require Import BeePL_aggregate_parameter_heap BeePL_scalar_parameter_heap BeePL_bytes_parameter_heap.
Require Import BeePL_packet_copy BeePL_copy_array_views BeePL_copy_array_coverage BeePL_copy_parameter_binding.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_mutation BeePL_aggregate_memory BeePL_object_paths.
Import ListNotations.
Local Open Scope Z_scope.

Record prepared_parameter_slot ge Sigma callee m objects cells packets id ty v target
    final objects' cells' packets' : Prop := {
  prepared_slot_execution : bind_variables ge callee m [(id,ty)] [v] final;
  prepared_slot_evolution : initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells' packets';
  prepared_slot_coherent : coherent_layout cells';
  prepared_slot_binding : packet_variable_binding ge Sigma callee cells' objects' packets' id ty;
  prepared_slot_cell_origin : forall b ofs t chunk,cells' b ofs t chunk ->cells b ofs t chunk \/ b=target;
  prepared_slot_object_origin : forall b ofs t,objects' b ofs t ->objects b ofs t \/ b=target;
  prepared_slot_packet_origin : forall b ofs,packets' b ofs ->packets b ofs \/ b=target;
  prepared_slot_view_origin : forall b ofs view,packets' b ofs ->packet_descriptor_valid final b ofs view ->
    exists old oldofs,packets old oldofs /\packet_descriptor_valid m old oldofs view
}.

Lemma copied_parameter_assignment_result : forall ge ty m b ofs v final result,
  is_aggregate_type ty=true ->assign_addr ge ty m b ofs Full v final result ->result=v.
Proof.
  intros ge ty m b ofs v final result Hkind Hassign. inversion Hassign;subst;try reflexivity;
    destruct ty;simpl in Hkind;try discriminate;
    match goal with H:access_mode_type _=By_value _|-_=>discriminate H end.
Qed.

Theorem initialize_admitted_parameter_slot : forall ge p Gamma Sigma caller m objects cells packets
    id ty v target callee,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->coherent_layout cells ->
  storage_type_check ge.(genv_cenv) ty=true ->type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty ->
  value_locations(packet_heap_locations ge cells objects packets) v ty ->
  Sigma ! target=Some ty ->callee ! id=Some(target,ty) ->
  source_block_extent m target(sizeof_type ge.(genv_cenv) ty) ->
  ((is_aggregate_type ty=true \/ty=Bytes)->array_copy_source ge.(genv_cenv) cells packets m target ty v) ->
  (forall b base root,objects b base root ->b<>target) ->
  (forall b ofs root ch,cells b ofs root ch ->b<>target) ->packet_block_disjoint m packets target ->
  exists final objects' cells' packets',
    prepared_parameter_slot ge Sigma callee m objects cells packets id ty v target final objects' cells' packets'.
Proof.
  intros ge p Gamma Sigma caller m objects cells packets id ty v target callee Henv Hheap Hcoherent
    Hstorage Htyped Hloc Hsigma Hget Hextent Hsource HobjectsApart HcellsApart HpacketsApart.
  pose proof(initialized_heap_packets _ _ _ _ _ _ _ _ Hheap) as Hpacket.
  pose proof(packet_heap_valid _ _ _ _ _ _ Hpacket) as Hvalid.
  destruct(admitted_data_storage_mode _ _ Hstorage) as [Hunit|[Hscalar|[Haggregate|Hbytes]]].
  - subst ty. assert(v=Vunit) by(inversion Htyped;reflexivity). subst v.
    exists m,objects,cells,packets;constructor.
    + eapply bind_variables_unit;[exact Hget|constructor].
    + eapply initialized_heap_evolution_refl;exact Hheap.
    + exact Hcoherent.
    + constructor;eapply callable_variable_data;[left;exact Hget|constructor|reflexivity].
    + intros;left;assumption.
    + intros;left;assumption.
    + intros;left;assumption.
    + intros b ofs view Hin Hv;exists b,ofs;auto.
  - destruct Hscalar as [chunk Hmode].
    destruct(initialize_preallocated_scalar_parameter ge Gamma Sigma caller m objects cells packets id ty v target callee chunk
      Hheap Hcoherent Hmode Hstorage Htyped Hloc Hsigma Hget Hextent HobjectsApart HcellsApart HpacketsApart)
      as [final [Hbind [Hevolution Hcoherent']]].
    exists final,objects,(extend_scalar_layout cells target Ptrofs.zero ty chunk),packets;constructor;try assumption.
    + constructor;eapply callable_variable_data;[left;exact Hget| |].
      * eapply heap_variable_scalar;right;repeat split;reflexivity.
      * destruct ty;try reflexivity;discriminate Hmode.
    + intros b ofs t ch [Hold|[Hb Hrest]];auto.
    + intros;left;assumption.
    + intros;left;assumption.
    + assert(Hnonunit:ty<>Utype) by(intro Heq;subst;discriminate Hmode).
      destruct(bind_parameters_singleton_result _ _ _ _ _ _ _ Hbind Hnonunit) as [written [result [Hlookup Hassign]]].
      rewrite Hget in Hlookup;inversion Hlookup;subst written.
      destruct(packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hvalid HpacketsApart Hassign) as [Hv Hviews].
      intros b ofs vw Hin Hview;exists b,ofs;split;[exact Hin|]. eapply preserved_packet_view_origin;eauto.
  - destruct(initialize_preallocated_aggregate_parameter ge p Gamma Sigma caller m objects cells packets id ty v target callee
      Henv Hheap Hcoherent Haggregate Hsigma Hget Hextent (Hsource(or_introl Haggregate))
      HobjectsApart HcellsApart HpacketsApart) as [final [after [Hbind [Hevolution [Hcoherent' Horigin]]]]].
    exists final,(add_aggregate_descriptor objects target Ptrofs.zero ty),after,
      (copied_object_packets ge.(genv_cenv) packets ty target);constructor;try assumption.
    + eapply packet_variable_aggregate;[left;exact Hget|exact Haggregate|right;repeat split;reflexivity].
    + intros b ofs t [Hold|[Hb Hrest]];auto.
    + intros b ofs [Hold|[Hb Hrest]];auto.
    + assert(Hnonunit:ty<>Utype) by(intro Heq;subst;discriminate Haggregate).
      destruct(bind_parameters_singleton_result _ _ _ _ _ _ _ Hbind Hnonunit) as [written [result [Hlookup Hassign]]].
      rewrite Hget in Hlookup;inversion Hlookup;subst written.
      assert(result=v) by(eapply copied_parameter_assignment_result;eauto). subst result.
      assert(Hhelper:sem_array_init_helper ge m target Ptrofs.zero [v] ty final)
        by(econstructor;[exact Hassign|constructor]).
      pose proof(source_extent_bound _ _ _ Hextent) as Hsize.
      intros b ofs view Hin Hview.
      eapply copy_array_packet_view_origins with(seed:=cells)(seed_packets:=packets)(values:=[v])
        (root:=ty)(dst:=target)(offset:=Ptrofs.zero);
        [exact Hhelper|auto|exact(proj1 Hsize)|constructor;[apply Hsource;auto|constructor]| | |exact Hvalid| |auto| |exact Hview].
      * rewrite Ptrofs.unsigned_zero;change(0+1*sizeof_type ge.(genv_cenv) ty<=Ptrofs.max_unsigned);lia.
      * rewrite Ptrofs.unsigned_zero,Henv;apply program_fresh_array_leaf_alignment;rewrite <-Henv;exact(proj1 Hsize).
      * intros old oldofs Hold;destruct(HpacketsApart _ _ Hold) as [Hb Hv];split;[left;exact Hb|exact Hv].
      * destruct Hin as [Hold|[Hb [delta [Hpath Ho]]]];[left;exact Hold|].
        right;exists 0%nat,delta;split;[simpl;lia|]. split;[exact Hpath|]. split;[exact Hb|].
        rewrite Ptrofs.unsigned_zero;cbn [Z.of_nat];rewrite Z.mul_0_l,?Z.add_0_l;exact Ho.
  - subst ty. destruct(Hsource(or_intror eq_refl)) as [src source Hv Hneq Hsrc Hbound Halign Hread Hleaves Hregions HsourcePackets].
    subst v.
    assert(Hregistered:packets src source).
    { specialize(HsourcePackets 0 ltac:(constructor;change(0<=packet_descriptor_size);pose proof packet_descriptor_size_positive;lia)).
      rewrite Z.add_0_r,Ptrofs.repr_unsigned in HsourcePackets;exact HsourcePackets. }
    destruct(initialize_preallocated_bytes_parameter ge Gamma Sigma caller m objects cells packets id src source target callee
      Hheap Hregistered Hsigma Hget Hextent HobjectsApart HcellsApart HpacketsApart) as [final [Hbind Hevolution]].
    exists final,objects,cells,(extend_packet_locations packets target Ptrofs.zero);constructor;try assumption.
    + eapply packet_variable_bytes;[left;exact Hget|reflexivity|right;auto].
    + intros;left;assumption.
    + intros;left;assumption.
    + intros b ofs [Hold|[Hb Ho]];auto.
    + destruct(bind_parameters_singleton_result _ _ _ _ _ _ _ Hbind ltac:(discriminate)) as [written [result [Hlookup Hassign]]].
      rewrite Hget in Hlookup;inversion Hlookup;subst written.
      eapply bytes_assignment_packet_view_origin;[exact Hvalid|exact Hregistered| |exact Hassign].
      intros b ofs Hin;destruct(HpacketsApart _ _ Hin) as [Hb Hv];split.
      * right;right;left;exact Hb.
      * intros vw Hvw;right;left;apply Hv;exact Hvw.
Qed.
