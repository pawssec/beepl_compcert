(* Constructive copying array fold. Sources are in old blocks; destination
   prefix invariants describe already initialized slots only. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initializer_slot BeePL_initializer_frames BeePL_layout_coherence.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy.
Require Import BeePL_packet_heap BeePL_packet_mutation BeePL_object_paths BeePL_storage_types.
Require Import BeePL_scalar_object_layout BeePL_structure_proofs BeePL_general_array_initialization.
Require Import BeePL_layout_proofs BeePL_bytes_layout.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pointer_blockcopy_alignment : forall env ptr,
  alignof_blockcopy env(transBeePL_ptr_type ptr)=align_chunk Mptr.
Proof.
  intros env ptr;induction ptr; simpl;auto.
  destruct b;try destruct p;try destruct i;reflexivity.
Qed.

Lemma program_storage_copy_alignment : forall p ty,
  alignof_blockcopy(bcomposite_composite_env p.(prog_comp_env))(transBeePL_type ty)=
    storage_copy_alignment p.(prog_comp_env) ty.
Proof.
  intros p ty;induction ty;simpl;try reflexivity.
  - destruct p0;try destruct i;try destruct s;reflexivity.
  - apply pointer_blockcopy_alignment.
  - rewrite translated_composite_lookup. destruct(PTree.get i p.(prog_comp_env));reflexivity.
  - exact IHty.
  - apply program_bytes_copy_alignment.
Qed.

Lemma program_initializer_copy_stride : forall p root,
  ((if is_bytes root then align_chunk Mptr else
      alignof_blockcopy(bcomposite_composite_env p.(prog_comp_env))(transBeePL_type root))|
      sizeof_type p.(prog_comp_env) root).
Proof.
  intros p root. rewrite program_storage_copy_alignment.
  destruct root;apply source_storage_copy_stride.
Qed.

Definition copied_array_cell env (seed:scalar_layout) values root (dst:Values.block) start b ofs ty chunk : Prop :=
  exists index src source old delta,
    nth_error values index=Some(Vloc src source) /\ seed src old ty chunk /\
    Ptrofs.unsigned old=Ptrofs.unsigned source+delta /\
    0<=delta /\ delta+size_chunk(transl_bchunk_cchunk chunk)<=sizeof_type env root /\
    b=dst /\ ofs=Ptrofs.repr(start+Z.of_nat index*sizeof_type env root+delta).

Theorem initialize_copy_array_elements :
  forall ge p Sigma L root values seed seed_packets m dst offset cells packets,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  is_aggregate_type root=true \/ root=Bytes -> 0<=sizeof_type ge.(genv_cenv) root ->
  Forall(array_copy_source ge.(genv_cenv) seed seed_packets m dst root) values ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets -> array_cells_prefix cells dst(Ptrofs.unsigned offset) ->
  array_packet_prefix m packets dst(Ptrofs.unsigned offset) ->
  (forall b ofs ty chunk,seed b ofs ty chunk -> cells b ofs ty chunk) ->
  (forall b ofs ty chunk,cells b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) ->
  (forall b ofs,seed_packets b ofs -> packets b ofs) -> Mem.valid_block m dst ->
  Mem.range_perm m dst(Ptrofs.unsigned offset)
    (Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root) Cur Freeable ->
  ((if is_bytes root then align_chunk Mptr else
    alignof_blockcopy(bcomposite_composite_env ge.(genv_cenv))(transBeePL_type root))|Ptrofs.unsigned offset) ->
  Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned ->
  array_copy_leaf_alignment ge.(genv_cenv) root(Ptrofs.unsigned offset)(length values) ->
  exists final after after_packets,
    sem_array_init_helper ge m dst offset values root final /\
    typed_memory_layout ge.(genv_cenv) Sigma after final /\ memory_locations L after final /\ coherent_layout after /\
    packet_state_valid final after_packets /\
    array_cells_prefix after dst(Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root) /\
    array_packet_prefix final after_packets dst(Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root) /\
    (forall b ofs ty chunk,cells b ofs ty chunk -> after b ofs ty chunk) /\
    (forall b ofs,packets b ofs -> after_packets b ofs) /\
    (forall b ofs ty chunk,after b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) /\
    (forall index delta ty chunk,(index<length values)%nat -> scalar_object_leaf ge.(genv_cenv) root delta ty chunk ->
      exists stored,after dst(Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta)) ty stored /\
        transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) /\
    (forall index delta,(index<length values)%nat -> object_path ge.(genv_cenv) root delta Bytes ->
      after_packets dst(Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta))) /\
    (forall b ofs ty chunk,after b ofs ty chunk -> cells b ofs ty chunk \/
      copied_array_cell ge.(genv_cenv) seed values root dst(Ptrofs.unsigned offset) b ofs ty chunk).
Proof.
  intros ge p Sigma L root values seed seed_packets.
  induction values as [|v values IH];intros m dst offset cells packets Henv Hkind Hsize Hsources
    Hcells Hlocations Hcoherent Hpackets Hprefix HpacketPrefix Hseed Horigin HseedPackets Hdst Hfree Halign Hbound HleafAlign.
  - exists m,cells,packets. split;[constructor|].
    split;[exact Hcells|]. split;[exact Hlocations|]. split;[exact Hcoherent|]. split;[exact Hpackets|].
    cbn [length Z.of_nat]. rewrite Z.mul_0_l,Z.add_0_r.
    split;[exact Hprefix|]. split;[exact HpacketPrefix|]. split;[auto|]. split;[auto|]. split;[exact Horigin|].
    split;[intros;lia|]. split;[intros;lia|]. intros;left;assumption.
  - inversion Hsources as [|head tail Hhead Htail];subst head tail.
    destruct Hhead as [src source Hv Hapart HsourceValid HsourceBound HsourceAlign HsourceRead HsourceLeaves HsourceRegions HsourcePackets].
    subst v.
    assert(Hend:Ptrofs.unsigned offset+sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned).
    { cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia. }
    assert(Htarget:Ptrofs.unsigned offset+sizeof_type ge.(genv_cenv) root<=Ptrofs.modulus)
      by(unfold Ptrofs.max_unsigned in Hend;lia).
    assert(Hready:initializer_copy_ready ge m root src source dst offset).
    { constructor;try assumption. left;exact Hapart.
      intros position Hin;apply Hfree. cbn [length];rewrite Nat2Z.inj_succ;nia. }
    pose proof(array_cells_prefix_separated _ _ _ (sizeof_type ge.(genv_cenv) root) Hprefix) as Haway.
    assert(HslotAlign:slot_copy_alignment cells src(Ptrofs.unsigned source)(Ptrofs.unsigned offset)(sizeof_type ge.(genv_cenv) root)).
    { destruct(Z_lt_le_dec 0(sizeof_type ge.(genv_cenv) root)) as [Hpositive|Hzero].
      - eapply array_current_source_alignment;[exact Hapart|exact Horigin| |].
        + replace(Ptrofs.unsigned source) with(Ptrofs.unsigned source+0) by lia.
          apply (HsourceRegions Hpositive);constructor;exact Hsize.
        + intros delta ty chunk Hleaf. destruct(HleafAlign 0%nat ltac:(simpl;lia)) as [Hs Hp].
          specialize(Hs _ _ _ Hleaf). cbn [Z.of_nat] in Hs;rewrite Z.mul_0_l,Z.add_0_r in Hs;exact Hs.
      - intros old ty chunk delta Hcell Hoff Hd Hlimit.
        pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia. }
    assert(HbytesCovered:forall delta,object_path ge.(genv_cenv) root delta Bytes ->packets src(Ptrofs.repr(Ptrofs.unsigned source+delta)))
      by(intros;apply HseedPackets;apply HsourcePackets;assumption).
    assert(HbytesAligned:forall delta,object_path ge.(genv_cenv) root delta Bytes ->(align_chunk Mptr|Ptrofs.unsigned offset+delta)).
    { intros delta Hpath. destruct(HleafAlign 0%nat ltac:(simpl;lia)) as [Hs Hp].
      specialize(Hp _ Hpath). cbn [Z.of_nat] in Hp;rewrite Z.mul_0_l,Z.add_0_r in Hp;exact Hp. }
    destruct(initialize_copy_slot ge Sigma L cells packets m root src source dst offset Hready Hcells Hlocations Haway HslotAlign Hpackets
      HbytesCovered HbytesAligned(array_packet_prefix_separated _ _ _ _ _ HpacketPrefix))
      as [written [bytes [Hread [Hstore [Hassign [Hcells' [Hlocations' Hpackets']]]]]]].
    set(newcells:=slot_copy_layout cells src(Ptrofs.unsigned source) dst(Ptrofs.unsigned offset)(sizeof_type ge.(genv_cenv) root)).
    set(newpackets:=slot_copy_packets ge.(genv_cenv) packets root dst(Ptrofs.unsigned offset)).
    set(next:=Ptrofs.add offset(Ptrofs.repr(sizeof_type ge.(genv_cenv) root))).
    assert(Hnext:Ptrofs.unsigned next=Ptrofs.unsigned offset+sizeof_type ge.(genv_cenv) root).
    { assert(Hsmall:0<=sizeof_type ge.(genv_cenv) root<=Ptrofs.max_unsigned)
        by(pose proof(Ptrofs.unsigned_range offset);lia).
      unfold next,Ptrofs.add. rewrite(Ptrofs.unsigned_repr _ Hsmall).
      apply Ptrofs.unsigned_repr;pose proof(Ptrofs.unsigned_range offset);lia. }
    assert(HendAll:Ptrofs.unsigned next+Z.of_nat(length values)*sizeof_type ge.(genv_cenv) root=
      Ptrofs.unsigned offset+Z.of_nat(length(Vloc src source::values))*sizeof_type ge.(genv_cenv) root).
    { rewrite Hnext. cbn [length];rewrite Nat2Z.inj_succ;ring. }
    destruct(IH written dst next newcells newpackets Henv Hkind Hsize) as
      [final [after [after_packets [Hhelper [Htyped [Hlocated [Hcoherent' [HpacketValid [Hprefix' [HpacketPrefix' [Hinc [Hpinc [Horigin' [Hcovered' [Hbytes' Hprovenance]]]]]]]]]]]]]]].
    + eapply array_copy_sources_assignment_frame;[exact Htail|exact Hassign].
    + exact Hcells'.
    + exact Hlocations'.
    + unfold newcells;apply slot_copy_layout_coherent;try assumption;pose proof(Ptrofs.unsigned_range offset);lia.
    + exact Hpackets'.
    + rewrite Hnext. unfold newcells;apply array_copy_cells_prefix;try assumption;pose proof(Ptrofs.unsigned_range offset);lia.
    + rewrite Hnext. unfold newpackets;eapply (array_copy_packet_prefix ge.(genv_cenv) root packets m written src (Ptrofs.unsigned source) dst (Ptrofs.unsigned offset) bytes); eauto;pose proof(Ptrofs.unsigned_range source);pose proof(Ptrofs.unsigned_range offset);lia.
    + intros;left;apply Hseed;assumption.
    + unfold newcells;eapply array_copy_cells_origin;exact Horigin.
    + intros;left;apply HseedPackets;assumption.
    + eapply assignment_preserves_valid_blocks;eauto.
    + rewrite Hnext. intros position Hin;eapply assignment_preserves_permissions;[exact Hassign|apply Hfree].
      cbn [length];rewrite Nat2Z.inj_succ;nia.
    + rewrite Hnext. apply Z.divide_add_r;[exact Halign|]. rewrite Henv;apply program_initializer_copy_stride.
    + rewrite HendAll;exact Hbound.
    + intros index Hindex. specialize(HleafAlign(S index) ltac:(simpl;lia)).
      replace(Ptrofs.unsigned next+Z.of_nat index*sizeof_type ge.(genv_cenv) root)
        with(Ptrofs.unsigned offset+Z.of_nat(S index)*sizeof_type ge.(genv_cenv) root)
        by(rewrite Hnext,Nat2Z.inj_succ;ring). exact HleafAlign.
    + exists final,after,after_packets. split;[eapply sem_allocate_array_elm;eauto|].
      split;[exact Htyped|]. split;[exact Hlocated|]. split;[exact Hcoherent'|]. split;[exact HpacketValid|].
      rewrite <-HendAll. split;[exact Hprefix'|]. split;[exact HpacketPrefix'|].
      split;[intros;apply Hinc;left;assumption|]. split;[intros;apply Hpinc;left;assumption|].
      split;[exact Horigin'|]. split.
      * intros [|index] delta ty chunk Hindex Hleaf.
        -- cbn [Z.of_nat]. rewrite Z.mul_0_l,Z.add_0_r.
           assert(Hcoverage:forall d t ch,scalar_object_leaf ge.(genv_cenv) root d t ch ->
             exists st,cells src(Ptrofs.repr(Ptrofs.unsigned source+d)) t st /\
               transl_bchunk_cchunk st=transl_bchunk_cchunk ch).
           { intros d t ch Hl. destruct(HsourceLeaves _ _ _ Hl) as [st [Hc Heq]].
             exists st;split;[apply Hseed;exact Hc|exact Heq]. }
           destruct(slot_copy_scalar_leaf_coverage ge.(genv_cenv) cells src(Ptrofs.unsigned source) dst(Ptrofs.unsigned offset) root
             ltac:(pose proof(Ptrofs.unsigned_range source);lia) HsourceBound Hcoverage delta ty chunk Hleaf)
             as [stored [Hcell Hsame]].
           exists stored;split;[apply Hinc;exact Hcell|exact Hsame].
        -- replace(Ptrofs.unsigned offset+Z.of_nat(S index)*sizeof_type ge.(genv_cenv) root+delta)
             with(Ptrofs.unsigned next+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta)
             by(rewrite Hnext,Nat2Z.inj_succ;ring). eapply Hcovered';[simpl in Hindex;lia|exact Hleaf].
      * split.
        -- intros [|index] delta Hindex Hpath.
           ++ cbn [Z.of_nat]. rewrite Z.mul_0_l,Z.add_0_r. apply Hpinc. right;split;[reflexivity|exists delta;auto].
           ++ replace(Ptrofs.unsigned offset+Z.of_nat(S index)*sizeof_type ge.(genv_cenv) root+delta)
             with(Ptrofs.unsigned next+Z.of_nat index*sizeof_type ge.(genv_cenv) root+delta)
             by(rewrite Hnext,Nat2Z.inj_succ;ring). eapply Hbytes';[simpl in Hindex;lia|exact Hpath].
        -- intros b ofs ty chunk Hcell. destruct(Hprovenance _ _ _ _ Hcell) as [Hheadcell|Htailcell].
           ++ destruct Hheadcell as [Hold|[Hb [old [delta [Hsourcecell [HsourceOffset [Hd [Hinside Hofs]]]]]]]].
              ** left;exact Hold.
              ** right. exists 0%nat,src,source,old,delta.
                 split;[reflexivity|]. split.
                 --- eapply array_copy_source_cells_are_seed;[exact Hapart|exact Horigin|exact Hsourcecell].
                 --- split;[exact HsourceOffset|]. split;[exact Hd|]. split;[exact Hinside|]. split;[exact Hb|].
                     cbn [Z.of_nat]. rewrite Z.mul_0_l,Z.add_0_r;exact Hofs.
           ++ right. destruct Htailcell as [index [sourceBlock [sourceOffset [old [delta [Hnth [Hsourcecell [HsourceOffset [Hd [Hinside [Hb Hofs]]]]]]]]]]].
              exists(S index),sourceBlock,sourceOffset,old,delta.
              split;[exact Hnth|]. split;[exact Hsourcecell|]. split;[exact HsourceOffset|].
              split;[exact Hd|]. split;[exact Hinside|]. split;[exact Hb|].
              rewrite Hofs,Hnext,Nat2Z.inj_succ;f_equal;ring.
Qed.
