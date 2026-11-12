(* Heterogeneous data-parameter binding. Inputs describe values and actual
   allocated memory; no assumption predicts success of a later assignment. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_block_extents BeePL_heap_extents BeePL_storage_types BeePL_object_paths.
Require Import BeePL_general_array_initialization BeePL_initializer_slot BeePL_initializer_frames.
Require Import BeePL_scalar_parameters BeePL_option_representation BeePL_structure_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma admitted_data_storage_mode : forall env ty,
  storage_type_check env ty=true ->
  ty=Utype \/ (exists chunk,access_mode_type ty=By_value(transl_bchunk_cchunk chunk)) \/
  is_aggregate_type ty=true \/ ty=Bytes.
Proof.
  intros env ty Hstore. destruct ty.
  - auto.
  - right;left;exists(chunk_of_ptype p). destruct p;try reflexivity;destruct i;destruct s;reflexivity.
  - right;left;exists option_pointer_chunk. rewrite option_pointer_chunk_translation;reflexivity.
  - right;right;left;reflexivity.
  - right;right;left;reflexivity.
  - rewrite storage_type_function_rejected in Hstore;discriminate.
  - auto.
Qed.

Lemma ready_parameter_copy_total : forall ge m root src source dst,
  initializer_copy_ready ge m root src source dst Ptrofs.zero ->
  exists final,assign_addr ge root m dst Ptrofs.zero Full(Vloc src source) final(Vloc src source).
Proof.
  intros ge m root src source dst [Hkind Hsize Hsrc Hdst HsrcBound HdstBound HsrcAlign HdstAlign Hapart Hread Hfree].
  destruct(Mem.range_perm_loadbytes m src(Ptrofs.unsigned source)(sizeof_type ge.(genv_cenv) root) Hread) as [bytes Hbytes].
  assert(Hlength:Z.of_nat(length bytes)=sizeof_type ge.(genv_cenv) root)
    by(rewrite(Mem.loadbytes_length _ _ _ _ _ Hbytes),Z2Nat.id;auto).
  assert(Hwrite:Mem.range_perm m dst(Ptrofs.unsigned Ptrofs.zero)
    (Ptrofs.unsigned Ptrofs.zero+Z.of_nat(length bytes)) Cur Writable).
  { rewrite Hlength;intros ofs Hin;eapply Mem.perm_implies;[apply Hfree;exact Hin|constructor]. }
  destruct(Mem.range_perm_storebytes _ _ _ _ Hwrite) as [final Hstore].
  exists final. destruct Hkind as [Hkind|Hkind].
  - assert(Hnotbytes:is_bytes root=false) by(destruct root;simpl in Hkind;try discriminate;reflexivity).
    rewrite Hnotbytes in HsrcAlign,HdstAlign. eapply assign_addr_copy;eauto.
  - subst root;eapply assign_addr_bytes_copy;eauto.
Qed.

Definition general_parameter_inputs ge Gamma Sigma L vm m seed packets params values : Prop :=
  Forall2 (fun param v =>
    let '(id,ty):=param in
    storage_type_check ge.(genv_cenv) ty=true /\
    type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty /\ value_locations L v ty /\
    exists target,vm ! id=Some(target,ty) /\ source_block_extent m target(sizeof_type ge.(genv_cenv) ty) /\
      ((is_aggregate_type ty=true \/ ty=Bytes) -> array_copy_source ge.(genv_cenv) seed packets m target ty v)) params values.

Lemma general_parameter_inputs_assignment_frame : forall ge Gamma Sigma L vm m seed packets params values
    written root offset assigned final result,
  general_parameter_inputs ge Gamma Sigma L vm m seed packets params values ->
  assign_addr ge root m written offset Full assigned final result ->
  general_parameter_inputs ge Gamma Sigma L vm final seed packets params values.
Proof.
  intros ge Gamma Sigma L vm m seed packets params values written root offset assigned final result Hinputs Hass.
  induction Hinputs;constructor;auto.
  destruct x as [id ty]. destruct H as [Hstorage [Htyped [Hloc [target [Hget [Hextent Hcopy]]]]]].
  split;[exact Hstorage|]. split;[exact Htyped|]. split;[exact Hloc|]. exists target;split;[exact Hget|]. split.
  - eapply assignment_source_extent;eauto.
  - intros Hkind. destruct(Hcopy Hkind) as [src source Hv Hneq Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
    eapply array_copy_source_intro with(src:=src)(source:=source);try assumption.
    + eapply assignment_preserves_valid_blocks;eauto.
    + intros position Hin;eapply assignment_preserves_permissions;[exact Hass|apply Hread;exact Hin].
Qed.

Theorem general_data_parameter_binding_total : forall ge Gamma Sigma L vm m seed packets params values,
  general_parameter_inputs ge Gamma Sigma L vm m seed packets params values ->
  exists final,bind_variables ge vm m params values final.
Proof.
  intros ge Gamma Sigma L vm m seed packets params values Hinputs. revert values m Hinputs.
  induction params as [|[id ty] params IH];intros values m Hinputs.
  - inversion Hinputs;subst;exists m;constructor.
  - inversion Hinputs as [|param v rest tail Hhead Htail];subst.
    destruct Hhead as [Hstorage [Htyped [Hloc [target [Hget [Hextent Hcopy]]]]]].
    destruct(admitted_data_storage_mode _ _ Hstorage) as [Hunit|[Hscalar|Hkind]].
    + subst ty. assert(v=Vunit) by(inversion Htyped;reflexivity). subst v.
      destruct(IH _ _ Htail) as [final Hbind]. exists final;eapply bind_variables_unit;eauto.
    + destruct Hscalar as [chunk Hmode].
      assert(Haccess:Mem.valid_access m(transl_bchunk_cchunk chunk) target(Ptrofs.unsigned Ptrofs.zero) Freeable).
      { split;[|rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r].
        rewrite Ptrofs.unsigned_zero,Z.add_0_l.
        rewrite(scalar_type_chunk_size ge.(genv_cenv) _ _ Hmode).
        exact(source_extent_freeable _ _ _ Hextent). }
      destruct(initialize_typed_scalar_array_cell ge ge.(genv_cenv) Gamma Sigma L m target Ptrofs.zero ty chunk v
        Htyped Hloc Hmode (storage_type_nonvolatile _ _ Hstorage) Haccess)
        as [next [Hstore [Hassign Hrest]]].
      assert(Htail':general_parameter_inputs ge Gamma Sigma L vm next seed packets params tail)
        by(eapply general_parameter_inputs_assignment_frame;[exact Htail|exact Hassign]).
      destruct(IH _ _ Htail') as [final Hbind]. exists final;eapply bind_variables_cons;eauto.
    + destruct(Hcopy Hkind) as [src source Hv Hneq Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
      subst v.
      assert(Hready:initializer_copy_ready ge m ty src source target Ptrofs.zero).
      { constructor;try assumption.
        - exact(proj1(source_extent_bound _ _ _ Hextent)).
        - exact(source_extent_valid _ _ _ Hextent).
        - rewrite Ptrofs.unsigned_zero. pose proof(source_extent_bound _ _ _ Hextent).
          unfold Ptrofs.max_unsigned in H;lia.
        - rewrite Ptrofs.unsigned_zero;apply Z.divide_0_r.
        - auto.
        - rewrite Ptrofs.unsigned_zero,Z.add_0_l;exact(source_extent_freeable _ _ _ Hextent). }
      destruct(ready_parameter_copy_total _ _ _ _ _ _ Hready) as [next Hassign].
      assert(Htail':general_parameter_inputs ge Gamma Sigma L vm next seed packets params tail)
        by(eapply general_parameter_inputs_assignment_frame;[exact Htail|exact Hassign]).
      destruct(IH _ _ Htail') as [final Hbind]. exists final;eapply bind_variables_cons;eauto.
Qed.

Print Assumptions general_data_parameter_binding_total.

Require Import BeePL_array_copy_sources BeePL_initialized_runtime BeePL_packet_bindings BeePL_layout_coherence.
Require Import BeePL_parameter_storage_check BeePL_storage_parameter_allocations BeePL_parameter_allocations.
Require Import BeePL_allocation_proofs BeePL_substitution_proofs BeePL_parameter_extents.

Lemma copy_source_parameter_allocation_frame : forall ge Sigma vm m params callee allocated Sigma'
    env cells packets target root v,
  alloc_variables ge Sigma vm m params callee allocated Sigma' ->
  array_copy_source env cells packets m target root v ->
  array_copy_source env cells packets allocated target root v.
Proof.
  intros ge Sigma vm m params callee allocated Sigma' env cells packets target root v Ha.
  induction Ha;intros Hsource;auto. apply IHHa.
  unfold balloc in H. destruct(Mem.alloc m 0(sizeof_type ge.(genv_cenv) ty)) as [next fresh] eqn:Halloc.
  inversion H;subst. destruct Hsource as [src source Hv Hneq Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
  eapply array_copy_source_intro with(src:=src)(source:=source);try assumption.
  - eapply Mem.valid_block_alloc;eauto.
  - intros position Hin;eapply Mem.perm_alloc_1;[exact Halloc|apply Hread;exact Hin].
Qed.

Theorem allocated_general_parameter_inputs : forall ge p Gamma Sigma caller m objects cells packets
    params values initial callee allocated Sigma',
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  Forall(fun param=>storage_type_check ge.(genv_cenv)(snd param)=true) params ->
  NoDup(map fst params) ->
  Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
    value_locations(packet_heap_locations ge cells objects packets) v(snd param)) params values ->
  alloc_variables ge Sigma initial m params callee allocated Sigma' ->
  general_parameter_inputs ge Gamma Sigma' (packet_heap_locations ge cells objects packets)
    callee allocated cells packets params values.
Proof.
  intros ge p Gamma Sigma caller m objects cells packets params values initial callee allocated Sigma'
    Henv Hheap Hcoherent Hstorage Hnames Hvalues Ha.
  destruct Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  destruct(alloc_variables_store_extension _ _ _ _ _ _ _ _ Ha Hblocks) as [Hextension Hblocks'].
  destruct(parameter_allocation_slots _ _ _ _ _ _ _ _ Ha Hnames) as [Hslots Hdistinct].
  assert(HslotExtent:=storage_parameter_allocation_slots _ _ _ _ _ _ _ _ Ha Hnames Hstorage).
  unfold general_parameter_inputs.
  assert(Hall:forall id ty v,In(id,ty)params ->
    type_expr ge.(genv_cenv) Gamma Sigma(Val v ty) [] ty ->
    value_locations(packet_heap_locations ge cells objects packets) v ty ->
    storage_type_check ge.(genv_cenv) ty=true /\
    type_expr ge.(genv_cenv) Gamma Sigma'(Val v ty) [] ty /\
    value_locations(packet_heap_locations ge cells objects packets) v ty /\
    exists target,callee ! id=Some(target,ty) /\source_block_extent allocated target(sizeof_type ge.(genv_cenv) ty) /\
      ((is_aggregate_type ty=true \/ ty=Bytes)->array_copy_source ge.(genv_cenv) cells packets allocated target ty v)).
  { intros id ty v Hin Htyped Hlocated. split.
    - rewrite Forall_forall in Hstorage;exact(Hstorage(id,ty) Hin).
    - split;[eapply(proj2 typing_store_extension);eauto|]. split;[exact Hlocated|].
      destruct(Hslots _ _ Hin) as [target [Hget [Hfresh Hrest]]]. exists target;split;[exact Hget|]. split.
      + eapply HslotExtent;eauto.
      + intros Hkind;eapply copy_source_parameter_allocation_frame;[exact Ha|].
        eapply typed_located_array_copy_source;eauto. }
  clear Ha HslotExtent Hslots Hstorage Hnames Hdistinct.
  induction Hvalues;constructor.
  - destruct x as [id ty]. destruct H as [Ht Hl]. eapply Hall;[left;reflexivity|exact Ht|exact Hl].
  - apply IHHvalues. intros id ty v Hin Ht Hl. eapply Hall;[right;exact Hin|exact Ht|exact Hl].
Qed.

Theorem general_data_parameter_preparation_total : forall ge p Gamma Sigma caller m objects cells packets
    allparams params values initial,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_heap_state ge Gamma Sigma caller m objects cells packets -> coherent_layout cells ->
  parameters_storage_check ge.(genv_cenv) allparams=true -> incl params allparams ->
  Forall(fun param=>is_funtype(snd param)=false) params -> NoDup(map fst params) ->
  Forall2(fun param v=>type_expr ge.(genv_cenv) Gamma Sigma(Val v(snd param)) [] (snd param) /\
    value_locations(packet_heap_locations ge cells objects packets) v(snd param)) params values ->
  exists callee allocated final Sigma',
    alloc_variables ge Sigma initial m params callee allocated Sigma' /\
    bind_variables ge callee allocated params values final /\
    store_context_extends Sigma Sigma' /\
    heap_block_extents Sigma' final objects cells packets.
Proof.
  intros ge p Gamma Sigma caller m objects cells packets allparams params values initial
    Henv Hheap Hcoherent Hcheck Hin Hdata Hnames Hvalues.
  pose proof(parameters_storage_data_list _ _ _ Hcheck Hin Hdata) as Hstorage.
  destruct(data_parameter_allocation_total ge Sigma initial m params) as [callee [allocated [Sigma' Ha]]].
  pose proof(allocated_general_parameter_inputs ge p Gamma Sigma caller m objects cells packets params values initial
    callee allocated Sigma' Henv Hheap Hcoherent Hstorage Hnames Hvalues Ha) as Hinputs.
  destruct(general_data_parameter_binding_total _ _ _ _ _ _ _ _ _ _ Hinputs) as [final Hb].
  exists callee,allocated,final,Sigma'. split;[exact Ha|]. split;[exact Hb|]. split.
  - exact(proj1(alloc_variables_store_extension _ _ _ _ _ _ _ _ Ha(initialized_heap_blocks _ _ _ _ _ _ _ _ Hheap))).
  - eapply parameter_binding_extents;[exact Hb|]. eapply storage_parameter_allocation_heap_extents;
      [exact Ha|exact Hstorage|exact(initialized_heap_extents _ _ _ _ _ _ _ _ Hheap)].
Qed.

Print Assumptions general_data_parameter_preparation_total.
