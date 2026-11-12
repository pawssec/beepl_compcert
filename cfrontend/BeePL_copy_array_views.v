(* Endpoint-view provenance for actual copying initializer executions. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_state BeePL_packet_mutation.
Require Import BeePL_initializer_slot BeePL_general_array_initialization BeePL_copy_array_initialization.
Require Import BeePL_aggregate_copy BeePL_object_paths BeePL_copy_array_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Lemma copy_assignment_storebytes : forall ge root m dst target value final,
  is_aggregate_type root=true \/ root=Bytes ->
  assign_addr ge root m dst target Full value final value ->
  exists bytes,Mem.storebytes m dst(Ptrofs.unsigned target) bytes=Some final.
Proof.
  intros ge root m dst target value final Hkind Hassign.
  inversion Hassign;subst;try solve[destruct Hkind as [Hkind|Hkind];simpl in Hkind;discriminate].
  - destruct Hkind as [Hkind|Hkind];[destruct root;simpl in Hkind;try discriminate|subst];
      match goal with H:access_mode_type _=By_value _|-_=>discriminate H end.
  - eexists;eassumption.
  - eexists;eassumption.
Qed.

Lemma copy_array_next_unsigned : forall env root (values:list value) offset,
  0<=sizeof_type env root ->
  Ptrofs.unsigned offset+Z.of_nat(S(length values))*sizeof_type env root<=Ptrofs.max_unsigned ->
  Ptrofs.unsigned(Ptrofs.add offset(Ptrofs.repr(sizeof_type env root)))=
    Ptrofs.unsigned offset+sizeof_type env root.
Proof.
  intros env root values offset Hsize Hbound.
  pose proof(Ptrofs.unsigned_range offset).
  rewrite Nat2Z.inj_succ in Hbound.
  assert(Hsmall:0<=sizeof_type env root<=Ptrofs.max_unsigned) by nia.
  unfold Ptrofs.add;rewrite(Ptrofs.unsigned_repr _ Hsmall).
  apply Ptrofs.unsigned_repr;nia.
Qed.

Theorem copy_array_descriptor_frame : forall ge m dst offset values root final,
  sem_array_init_helper ge m dst offset values root final ->
  is_aggregate_type root=true \/ root=Bytes -> 0<=sizeof_type ge.(genv_cenv) root ->
  Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned ->
  forall b ofs view,
  b<>dst \/ Ptrofs.unsigned ofs+packet_descriptor_size<=Ptrofs.unsigned offset ->
  packet_descriptor_valid m b ofs view -> packet_descriptor_valid final b ofs view.
Proof.
  intros ge m dst offset values root final Hhelper;induction Hhelper;
    intros Hkind Hsize Hbound b descriptor view Hapart Hview.
  - exact Hview.
  - destruct(copy_assignment_storebytes _ _ _ _ _ _ _ Hkind H) as [bytes Hstore].
    eapply IHHhelper;[exact Hkind|exact Hsize| | |].
    + rewrite(copy_array_next_unsigned _ _ vs ofs Hsize Hbound).
      cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia.
    + rewrite(copy_array_next_unsigned _ _ vs ofs Hsize Hbound);intuition lia.
    + eapply packet_descriptor_storebytes_disjoint;[exact Hstore|intuition|exact Hview].
  - destruct Hkind;discriminate.
Qed.

Lemma copy_assignment_bytes : forall ge m root src source dst target final,
  is_aggregate_type root=true \/ root=Bytes ->
  assign_addr ge root m dst target Full(Vloc src source) final(Vloc src source) ->
  exists bytes,Mem.loadbytes m src(Ptrofs.unsigned source)(sizeof_type ge.(genv_cenv) root)=Some bytes /\
    Mem.storebytes m dst(Ptrofs.unsigned target) bytes=Some final.
Proof.
  intros ge m root src source dst target final [Hkind|Hkind] Hassign.
  - apply(aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign).
  - subst root. destruct(bytes_assignment_memory_effect _ _ _ _ _ _ _ _ Hassign) as [bytes [Hr [Hw Hrest]]].
    exists bytes;split;assumption.
Qed.

Theorem copy_array_selected_view : forall ge seed packets root values m dst offset final,
  sem_array_init_helper ge m dst offset values root final ->
  is_aggregate_type root=true \/ root=Bytes -> 0<=sizeof_type ge.(genv_cenv) root ->
  Forall(array_copy_source ge.(genv_cenv) seed packets m dst root) values ->
  Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned ->
  array_copy_leaf_alignment ge.(genv_cenv) root(Ptrofs.unsigned offset)(length values) ->
  forall index src source delta view,
  nth_error values index=Some(Vloc src source) -> object_path ge.(genv_cenv) root delta Bytes ->
  packet_descriptor_valid m src(Ptrofs.repr(Ptrofs.unsigned source+delta)) view ->
  packet_descriptor_valid final dst
    (Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta)) view.
Proof.
  intros ge seed packets root values m dst offset final Hhelper.
  induction Hhelper;intros Hkind Hsize Hsources Hbound Halign index src source delta view Hnth Hpath Hview.
  - destruct index;discriminate.
  - inversion Hsources as [|head tail Hhead Htail];subst head tail.
    assert(Hnext:Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(sizeof_type ge.(genv_cenv) t)))=
      Ptrofs.unsigned ofs+sizeof_type ge.(genv_cenv) t)
      by(eapply copy_array_next_unsigned;[exact Hsize|exact Hbound]).
    assert(Htailbound:Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(sizeof_type ge.(genv_cenv) t)))+
      Z.of_nat(length vs)*sizeof_type ge.(genv_cenv) t<=Ptrofs.max_unsigned).
    { rewrite Hnext;cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia. }
    destruct index as [|index].
    + simpl in Hnth;inversion Hnth;subst v.
      destruct Hhead as [sourceBlock sourceOffset Hvalue Hapart Hvalid Hend HsourceAlign Hread Hleaves Hregions Hpackets].
      inversion Hvalue;subst sourceBlock sourceOffset.
      destruct(copy_assignment_bytes _ _ _ _ _ _ _ _ Hkind H) as [bytes [Hr Hw]].
      cbn [Z.of_nat];rewrite Z.mul_0_l,Z.add_0_r.
      eapply copy_array_descriptor_frame;[exact Hhelper|exact Hkind|exact Hsize|exact Htailbound| |].
      * right. rewrite Hnext. pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [Hs Hinside]].
        change(delta+packet_descriptor_size<=sizeof_type ge.(genv_cenv) t) in Hinside.
        rewrite Ptrofs.unsigned_repr;[lia|]. pose proof packet_descriptor_size_positive.
        pose proof(Ptrofs.unsigned_range ofs);unfold Ptrofs.max_unsigned in *;
          cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia.
      * eapply(slot_copied_descriptor ge.(genv_cenv) t m m' src(Ptrofs.unsigned source) loc(Ptrofs.unsigned ofs) bytes delta view);
          try eassumption.
        -- pose proof(Ptrofs.unsigned_range source);lia.
        -- pose proof(Ptrofs.unsigned_range ofs);lia.
        -- cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;unfold Ptrofs.max_unsigned in Hbound;nia.
        -- destruct(Halign 0%nat ltac:(simpl;lia)) as [_ Hb]. specialize(Hb _ Hpath).
           cbn [Z.of_nat] in Hb;rewrite Z.mul_0_l,Z.add_0_r in Hb;exact Hb.
    + replace(Ptrofs.unsigned ofs+Z.of_nat(S index)*sizeof_type ge.(genv_cenv) t+delta)
        with(Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(sizeof_type ge.(genv_cenv) t)))+
          Z.of_nat index*sizeof_type ge.(genv_cenv) t+delta) by(rewrite Hnext,Nat2Z.inj_succ;ring).
      eapply IHHhelper;[exact Hkind|exact Hsize| |exact Htailbound| |exact Hnth|exact Hpath|].
      * eapply array_copy_sources_assignment_frame;[exact Htail|exact H].
      * intros i Hi. specialize(Halign(S i) ltac:(simpl;lia)).
        replace(Ptrofs.unsigned(Ptrofs.add ofs(Ptrofs.repr(sizeof_type ge.(genv_cenv) t)))+
          Z.of_nat i*sizeof_type ge.(genv_cenv) t)
          with(Ptrofs.unsigned ofs+Z.of_nat(S i)*sizeof_type ge.(genv_cenv) t)
          by(rewrite Hnext,Nat2Z.inj_succ;ring). exact Halign.
      * assert(Hselected:array_copy_source ge.(genv_cenv) seed packets m loc t(Vloc src source)).
        { rewrite Forall_forall in Htail;apply Htail;eapply nth_error_In;exact Hnth. }
        destruct Hselected as [sourceBlock sourceOffset Hvalue Hapart Hrest].
        inversion Hvalue;subst sourceBlock sourceOffset.
        destruct(copy_assignment_storebytes _ _ _ _ _ _ _ Hkind H) as [bytes Hw].
        eapply packet_descriptor_storebytes_frame;[exact Hw|exact Hapart|exact Hview].
  - destruct Hkind;discriminate.
Qed.

Theorem copy_array_packet_view_origins : forall ge seed seed_packets packets root values m dst offset final,
  sem_array_init_helper ge m dst offset values root final ->
  is_aggregate_type root=true \/ root=Bytes -> 0<=sizeof_type ge.(genv_cenv) root ->
  Forall(array_copy_source ge.(genv_cenv) seed seed_packets m dst root) values ->
  Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned ->
  array_copy_leaf_alignment ge.(genv_cenv) root(Ptrofs.unsigned offset)(length values) ->
  packet_state_valid m packets -> array_packet_prefix m packets dst(Ptrofs.unsigned offset) ->
  (forall b ofs,seed_packets b ofs -> packets b ofs) ->
  forall b ofs view,copied_array_packets ge.(genv_cenv) packets values root dst(Ptrofs.unsigned offset) b ofs ->
  packet_descriptor_valid final b ofs view ->
  exists original original_offset,packets original original_offset /\ packet_descriptor_valid m original original_offset view.
Proof.
  intros ge seed seed_packets packets root values m dst offset final Hhelper Hkind Hsize Hsources Hbound Halign
    Hvalid Hprefix Hseed b ofs view Hregistered Hview.
  destruct Hregistered as [Hold|[index [delta [Hi [Hpath [Hb Hofs]]]]]].
  - destruct(Hvalid _ _ Hold) as [_ [oldview [contents [Holdview Hrest]]]].
    assert(Hpreserved:packet_descriptor_valid final b ofs oldview).
    { eapply copy_array_descriptor_frame;[exact Hhelper|exact Hkind|exact Hsize|exact Hbound| |exact Holdview].
      exact(proj1(Hprefix _ _ Hold)). }
    assert(view=oldview) by(eapply packet_descriptor_view_unique;eauto).
    subst view;exists b,ofs;auto.
  - subst b ofs. destruct(nth_error values index) as [v|] eqn:Hnth.
    2:{ apply nth_error_None in Hnth;lia. }
    assert(Hsource:array_copy_source ge.(genv_cenv) seed seed_packets m dst root v).
    { rewrite Forall_forall in Hsources;apply Hsources;eapply nth_error_In;exact Hnth. }
    destruct Hsource as [src source Hv Hapart HsourceValid HsourceBound HsourceAlign Hread Hleaves Hregions HsourcePackets].
    subst v. pose proof(Hseed _ _(HsourcePackets _ Hpath)) as HsourceRegistered.
    destruct(Hvalid _ _ HsourceRegistered) as [_ [oldview [contents [Holdview Hrest]]]].
    assert(Hcopied:packet_descriptor_valid final dst
      (Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta)) oldview).
    { eapply copy_array_selected_view; eauto. }
    assert(view=oldview) by(eapply packet_descriptor_view_unique;eauto).
    subst view. exists src,(Ptrofs.repr(Ptrofs.unsigned source+delta));auto.
Qed.
