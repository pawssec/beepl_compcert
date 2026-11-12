(* Actual heterogeneous binding fold over the complete shared heap invariant. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_parameter_slot_heap BeePL_initialized_runtime BeePL_packet_bindings BeePL_packet_heap.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_mutation.
Require Import BeePL_soundness_memory BeePL_substitution_proofs BeePL_soundness_store BeePL_runtime_locations BeePL_callable_variables BeePL_layout_coherence.
Require Import BeePL_general_array_initialization BeePL_call_bindings BeePL_block_extents BeePL_heap_extents BeePL_storage_types.
Require Import BeePL_scalar_object_layout BeePL_general_parameter_binding.
Import ListNotations.
Local Open Scope Z_scope.

Definition heap_parameter_input ge Gamma Sigma callee m objects cells packets universe
    (param:ident*type) (v:value) : Prop :=
  let '(id,ty):=param in
  storage_type_check ge.(genv_cenv) ty=true /\type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty /\
  value_locations(packet_heap_locations ge cells objects packets) v ty /\
  exists target,callee ! id=Some(target,ty) /\Sigma ! target=Some ty /\
    source_block_extent m target(sizeof_type ge.(genv_cenv) ty) /\
    (forall b base root,objects b base root ->b<>target) /\
    (forall b ofs root ch,cells b ofs root ch ->b<>target) /\packet_block_disjoint m packets target /\
    ((is_aggregate_type ty=true \/ty=Bytes)->array_copy_source ge.(genv_cenv) cells packets m target ty v) /\
    ((is_aggregate_type ty=true \/ty=Bytes)->forall src ofs,v=Vloc src ofs ->
      forall written,parameter_binding_target callee universe written ->src<>written).

Lemma packet_binding_evolution : forall ge Sigma objects cells packets final objects' cells' packets' callee id ty,
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells' packets' ->
  packet_variable_binding ge Sigma callee cells objects packets id ty ->
  packet_variable_binding ge Sigma callee cells' objects' packets' id ty.
Proof.
  intros * Hevol Hbinding;destruct Hbinding.
  - eapply packet_variable_callable. eapply callable_variable_binding_extend;
      [apply store_context_extends_refl| |eassumption].
    intros;eapply initialized_evolution_cells;[exact Hevol|eassumption].
  - eapply packet_variable_aggregate;[eassumption|eassumption|]. eapply initialized_evolution_objects;[exact Hevol|eassumption].
  - eapply packet_variable_bytes;[eassumption|eassumption|]. eapply initialized_evolution_packet_locations;[exact Hevol|eassumption].
Qed.

Lemma parameter_input_after_slot : forall ge Gamma Sigma callee m objects cells packets universe
    id ty v written final objects' cells' packets' other otherType otherValue,
  prepared_parameter_slot ge Sigma callee m objects cells packets id ty v written final objects' cells' packets' ->
  parameter_binding_target callee universe written ->
  heap_parameter_input ge Gamma Sigma callee m objects cells packets universe (other,otherType) otherValue ->
  (forall target,callee ! other=Some(target,otherType)->target<>written) ->
  heap_parameter_input ge Gamma Sigma callee final objects' cells' packets' universe (other,otherType) otherValue.
Proof.
  intros ge Gamma Sigma callee m objects cells packets universe id ty v written final objects' cells' packets'
    other otherType otherValue Hstep Hwritten Hinput Hneq.
  destruct Hinput as [Hstorage [Htyped [Hloc [target [Hget [Hsigma [Hextent [HobjApart [HcellApart [HpacketApart [Hsource Havoid]]]]]]]]]]].
  pose proof(prepared_slot_evolution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as Hevol.
  pose proof(prepared_slot_execution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as Hbind.
  split;[exact Hstorage|]. split;[exact Htyped|]. split.
  - eapply value_locations_monotone;[|exact Hloc]. eapply packet_heap_locations_monotone.
    + intros;eapply initialized_evolution_cells;[exact Hevol|eassumption].
    + intros;eapply initialized_evolution_objects;[exact Hevol|eassumption].
    + intros;eapply initialized_evolution_packet_locations;[exact Hevol|eassumption].
  - exists target;split;[exact Hget|]. split;[exact Hsigma|]. split.
    + eapply source_block_extent_transport;[exact Hextent| | |].
      * eapply bind_parameters_valid_blocks;[exact Hbind|exact(source_extent_valid _ _ _ Hextent)].
      * intros;eapply(proj2(bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind));eassumption.
      * intros;eapply(proj1(bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind));eassumption.
    + split.
      * intros b base root Hin. destruct(prepared_slot_object_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep _ _ _ Hin);
          [eapply HobjApart;eauto|subst;intro Heq;symmetry in Heq;exact(Hneq target Hget Heq)].
      * split.
        -- intros b ofs root ch Hin. destruct(prepared_slot_cell_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep _ _ _ _ Hin);
             [eapply HcellApart;eauto|subst;intro Heq;symmetry in Heq;exact(Hneq target Hget Heq)].
        -- split.
           ++ intros b ofs Hin;split.
              ** destruct(prepared_slot_packet_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep _ _ Hin);
                   [exact(proj1(HpacketApart _ _ H))|subst;intro Heq;symmetry in Heq;exact(Hneq target Hget Heq)].
              ** intros vw Hview. destruct(prepared_slot_view_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep _ _ _ Hin Hview)
                   as [old [oldofs [Hold Hbefore]]]. exact(proj2(HpacketApart _ _ Hold) _ Hbefore).
           ++ split;[|exact Havoid]. intros Hkind.
              destruct(Hsource Hkind) as [src source Hv Hapart Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
              eapply array_copy_source_intro with(src:=src)(source:=source);try assumption.
              ** eapply bind_parameters_valid_blocks;eauto.
              ** intros pos Hin;apply(proj2(bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind));apply Hread;exact Hin.
              ** intros delta leaf ch Hpath. destruct(Hleaves _ _ _ Hpath) as [stored [Hcell Heq]].
                 exists stored;split;[eapply initialized_evolution_cells;eauto|exact Heq].
              ** intros Hpositive delta child Hpath;eapply array_current_source_regions with(seed:=cells)(dst:=written).
                 --- eapply Havoid;[exact Hkind|exact Hv|exact Hwritten].
                 --- exact(prepared_slot_cell_origin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep).
                 --- apply Hregions;exact Hpositive.
                 --- exact Hpath.
              ** intros delta Hpath;eapply initialized_evolution_packet_locations;[exact Hevol|apply Hpackets;exact Hpath].
Qed.

Lemma singleton_bind_then_tail : forall ge callee m id ty v middle params values final,
  bind_variables ge callee m [(id,ty)] [v] middle ->
  bind_variables ge callee middle params values final ->
  bind_variables ge callee m ((id,ty)::params)(v::values) final.
Proof.
  intros * Hhead Htail. inversion Hhead;subst;
    match goal with H:bind_variables _ _ _ [] [] _|-_=>inversion H;subst end;
    [eapply bind_variables_cons|eapply bind_variables_unit];eauto.
Qed.

Theorem initialize_parameter_heap_fold : forall ge p Gamma Sigma caller callee universe params values m objects cells packets,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets ->coherent_layout cells ->
  incl params universe ->parameter_targets_distinct callee params ->
  Forall2(heap_parameter_input ge Gamma Sigma callee m objects cells packets universe) params values ->
  exists final objects' cells' packets',
    bind_variables ge callee m params values final /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells' packets' /\
    coherent_layout cells' /\
    forall id ty,In(id,ty)params ->packet_variable_binding ge Sigma callee cells' objects' packets' id ty.
Proof.
  intros ge p Gamma Sigma caller callee universe params;induction params as [|[id ty] params IH];
    intros values m objects cells packets Henv Hheap Hcoherent Hin Hdistinct Hinputs.
  - inversion Hinputs;subst. exists m,objects,cells,packets;split;[constructor|]. split.
    + eapply initialized_heap_evolution_refl;exact Hheap.
    + split;[exact Hcoherent|intros;contradiction].
  - inversion Hinputs as [|param v rest tail Hhead Htail];subst.
    destruct Hhead as [Hstorage [Htyped [Hloc [target [Hget [Hsigma [Hextent [HobjApart [HcellApart [HpacketApart [Hsource Havoid]]]]]]]]]]].
    destruct(initialize_admitted_parameter_slot ge p Gamma Sigma caller m objects cells packets id ty v target callee
      Henv Hheap Hcoherent Hstorage Htyped Hloc Hsigma Hget Hextent Hsource HobjApart HcellApart HpacketApart)
      as [middle [nextObjects [nextCells [nextPackets Hslot]]]].
    pose proof(prepared_slot_evolution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hslot) as Hstep.
    destruct Hdistinct as [Hnames HtargetUnique]. inversion Hnames as [|? ? Hnotin HtailNames];subst.
    assert(HtailDistinct:parameter_targets_distinct callee params).
    { split;[exact HtailNames|]. intros;eapply HtargetUnique;eauto;right;assumption. }
    assert(Htarget:parameter_binding_target callee universe target).
    { exists id,ty;split;[apply Hin;left;reflexivity|exact Hget]. }
    assert(HtailInputs:Forall2(heap_parameter_input ge Gamma Sigma callee middle nextObjects nextCells nextPackets universe) params tail).
    { assert(Hall:forall other t value,In(other,t)params ->
          heap_parameter_input ge Gamma Sigma callee m objects cells packets universe (other,t) value ->
          heap_parameter_input ge Gamma Sigma callee middle nextObjects nextCells nextPackets universe (other,t) value).
      { intros other t value Hmember Hinput;eapply parameter_input_after_slot;[exact Hslot|exact Htarget|exact Hinput|].
        intros otherTarget Hother Heq;subst otherTarget.
        assert(other=id) by(eapply HtargetUnique;[right;exact Hmember|left;reflexivity|exact Hother|exact Hget]).
        subst other;apply Hnotin;apply in_map with(f:=fst) in Hmember;exact Hmember. }
      clear IH Hinputs Hslot Htarget Hstep Hnames HtargetUnique Hnotin HtailNames HtailDistinct Hin.
      induction Htail;constructor.
      - destruct x as [other t];eapply Hall;[left;reflexivity|exact H].
      - apply IHHtail;intros;eapply Hall;[right;eassumption|eassumption]. }
    destruct(IH tail middle nextObjects nextCells nextPackets Henv
      (initialized_heap_state_evolve _ _ _ _ _ _ _ _ _ _ _ _ _ Hheap Hstep)
      (prepared_slot_coherent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hslot)
      ltac:(intros x Hx;apply Hin;right;exact Hx) HtailDistinct HtailInputs)
      as [final [finalObjects [finalCells [finalPackets [Hbind [Hrest [Hcoherent' Hbindings]]]]]]].
    exists final,finalObjects,finalCells,finalPackets;split.
    + eapply singleton_bind_then_tail;[exact(prepared_slot_execution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hslot)|exact Hbind].
    + split;[eapply initialized_heap_evolution_trans;[exact Hstep|exact Hrest]|]. split;[exact Hcoherent'|].
      intros name t [Heq|Hmember].
      * inversion Heq;subst;eapply packet_binding_evolution;[exact Hrest|exact(prepared_slot_binding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hslot)].
      * apply Hbindings;exact Hmember.
Qed.

Print Assumptions initialize_parameter_heap_fold.
