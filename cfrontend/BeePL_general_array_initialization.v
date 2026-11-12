(* General element traversal. The first fold handles every inhabited scalar
   storage type, including ordinary references and nullable code-pointer None.
   Aggregate/Bytes sources are kept distinct from freshly allocated storage. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_substitution_proofs BeePL_scalar_parameters BeePL_option_representation.
Require Import BeePL_initializer_slot BeePL_initializer_frames BeePL_layout_coherence.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_mutation.
Require Import BeePL_packet BeePL_packet_descriptor_copy.
Require Import BeePL_object_paths BeePL_storage_types BeePL_scalar_object_layout.
Require Import BeePL_structure_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma array_object_path_decomposition : forall env elem len attr delta ty,
  object_path env (Atype elem len attr) delta ty ->
  (delta=0 /\ ty=Atype elem len attr) \/
  exists index relative, 0<=index<len /\ delta=index*sizeof_type env elem+relative /\
    object_path env elem relative ty.
Proof.
  intros env elem len attr delta ty Hpath. remember (Atype elem len attr) as root eqn:Hroot.
  induction Hpath.
  - left; auto.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent]|[i [relative [Hi [Hbase Hchild]]]]];
      [discriminate Hparent|]. right. exists i,(relative+delta). split; [exact Hi|]. split; [lia|].
    eapply path_field; eauto.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent]|[i [relative [Hi [Hbase Hchild]]]]].
    + inversion Hparent; subst. right; exists index,0. repeat split; try assumption; try lia.
      constructor; assumption.
    + right; exists i,(relative+index*sizeof_type env ty). split; [exact Hi|]. split; [lia|].
      eapply path_array_element; eauto.
Qed.

Lemma initialized_scalar_chunk_unique : forall first second,
  transl_bchunk_cchunk first=transl_bchunk_cchunk second -> first=second.
Proof. destruct first,second; simpl; congruence. Qed.

Theorem initialize_typed_scalar_array_cell : forall ge env Gamma Sigma L m block offset ty chunk v,
  type_expr env Gamma Sigma (Val v ty) [] ty -> value_locations L v ty ->
  access_mode_type ty=By_value(transl_bchunk_cchunk chunk) ->
  type_is_volatile(transBeePL_type ty)=false ->
  Mem.valid_access m (transl_bchunk_cchunk chunk) block (Ptrofs.unsigned offset) Freeable ->
  exists final,
    Mem.store (transl_bchunk_cchunk chunk) m block (Ptrofs.unsigned offset) (trans_bvalue_cvalue v)=Some final /\
    assign_addr ge ty m block offset Full v final v /\
    typed_memory_cell env Sigma final block offset ty chunk /\
    (forall loaded,deref_addr ty final block offset Full loaded -> value_locations L loaded ty).
Proof.
  intros ge env Gamma Sigma L m block offset ty chunk v Htyped Hloc Hmode Hvol Haccess.
  destruct (typed_scalar_slot_cases _ _ _ _ _ _ Htyped Hmode Hvol) as [Hscalar|[args [effects [result [variadic [Hty Hv]]]]]].
  - assert (Hchunk : chunk=scalar_parameter_chunk ty).
    { apply initialized_scalar_chunk_unique. pose proof(scalar_parameter_chunk_access _ Hscalar); congruence. }
    subst chunk. eapply initialize_scalar_parameter; eauto.
  - subst ty v. assert (Hchunk : chunk=option_pointer_chunk).
    { apply initialized_scalar_chunk_unique. rewrite option_pointer_chunk_translation. simpl in Hmode; congruence. }
    subst chunk. rewrite option_pointer_chunk_translation in Haccess |- *.
    eapply initialize_null_function_option_cell; exact Haccess.
Qed.

Lemma scalar_array_stride : forall env ty chunk,
  access_mode_type ty=By_value(transl_bchunk_cchunk chunk) ->
  sizeof_type env ty=size_chunk(transl_bchunk_cchunk chunk) /\
  0<sizeof_type env ty /\ (align_chunk(transl_bchunk_cchunk chunk)|sizeof_type env ty).
Proof.
  intros env ty chunk Hmode. pose proof(scalar_type_chunk_size env ty (transl_bchunk_cchunk chunk) Hmode) as Hsize.
  rewrite <- Hsize. split; [reflexivity|]. split; [pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia|].
  destruct chunk; simpl; try apply Z.divide_refl; eexists; reflexivity.
Qed.

Lemma scalar_slot_extension_coherent : forall cells block offset ty chunk,
  coherent_layout cells ->
  slot_cells_disjoint cells block (Ptrofs.unsigned offset) (size_chunk(transl_bchunk_cchunk chunk)) ->
  coherent_layout(extend_scalar_layout cells block offset ty chunk).
Proof.
  intros cells block offset ty chunk Hcoherent Haway b ofs t ch Hcell old off t' ch' Hold.
  destruct Hcell as [Hcell|[Hb [Hofs [Ht Hch]]]];
    destruct Hold as [Hold|[Hob [Hoff [Ht' Hch']]]].
  - eapply Hcoherent; eauto.
  - subst. right. destruct(Haway _ _ _ _ Hcell); [left;congruence|right;tauto].
  - subst. right. destruct(Haway _ _ _ _ Hold); [left;assumption|right;tauto].
  - subst; left; auto.
Qed.

Lemma scalar_slot_remaining_disjoint : forall cells block offset ty chunk count,
  0<=count ->
  slot_cells_disjoint cells block (Ptrofs.unsigned offset)
    (size_chunk(transl_bchunk_cchunk chunk)+count) ->
  slot_cells_disjoint(extend_scalar_layout cells block offset ty chunk) block
    (Ptrofs.unsigned offset+size_chunk(transl_bchunk_cchunk chunk)) count.
Proof.
  intros cells block offset ty chunk count Hcount Haway b ofs t ch [Hold|[Hb [Ho [Ht Hch]]]].
  - destruct(Haway _ _ _ _ Hold) as [Hneq|[Hbefore|Hafter]];
      [left;exact Hneq|right;left;pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia|right;right;lia].
  - subst; right;left;lia.
Qed.

Lemma scalar_slot_memory_frame : forall env Sigma L cells m final block offset ty chunk v,
  typed_memory_layout env Sigma cells m -> memory_locations L cells m ->
  slot_cells_disjoint cells block (Ptrofs.unsigned offset) (size_chunk(transl_bchunk_cchunk chunk)) ->
  Mem.store (transl_bchunk_cchunk chunk) m block (Ptrofs.unsigned offset) (trans_bvalue_cvalue v)=Some final ->
  typed_memory_cell env Sigma final block offset ty chunk ->
  (forall loaded,deref_addr ty final block offset Full loaded -> value_locations L loaded ty) ->
  typed_memory_layout env Sigma(extend_scalar_layout cells block offset ty chunk) final /\
  memory_locations L(extend_scalar_layout cells block offset ty chunk) final.
Proof.
  intros env Sigma L cells m final block offset ty chunk v Hcells Hlocations Haway Hstore Hcell Hlocated.
  assert (Hold : forall b ofs t ch,cells b ofs t ch ->
    typed_memory_cell env Sigma final b ofs t ch /\
    forall value,deref_addr t final b ofs Full value -> value_locations L value t).
  { intros b ofs t ch Hin. pose proof(Haway _ _ _ _ Hin) as Hdisjoint. split.
    - eapply typed_memory_cell_store_disjoint; [apply Hcells;exact Hin|exact Hstore|tauto].
    - intros value Hread. destruct(Hcells _ _ _ _ Hin) as [Hmode Hvol Hperm [cv [old [Hload [Hdecode Htyped]]]]].
      assert(HoldRead:deref_addr t final b ofs Full old).
      { eapply deref_addr_value; eauto. simpl. rewrite(Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload|tauto]. }
      assert(value=old) by (eapply deref_full_deterministic;eauto). subst value.
      eapply Hlocations; [exact Hin|]. eapply deref_addr_value; eauto. }
  split.
  - intros b ofs t ch [Hin|[Hb [Ho [Ht Hch]]]]; [apply (proj1(Hold _ _ _ _ Hin))|subst;exact Hcell].
  - intros b ofs t ch [Hin|[Hb [Ho [Ht Hch]]]] value Hread;
      [eapply (proj2(Hold _ _ _ _ Hin));exact Hread|subst;eapply Hlocated;exact Hread].
Qed.

Definition array_scalar_values env Gamma Sigma L ty values :=
  Forall (fun v=>type_expr env Gamma Sigma(Val v ty) [] ty /\ value_locations L v ty) values.

Theorem initialize_scalar_array_elements :
  forall ge env Gamma Sigma L ty chunk values m block offset cells packets,
  array_scalar_values env Gamma Sigma L ty values ->
  access_mode_type ty=By_value(transl_bchunk_cchunk chunk) ->
  type_is_volatile(transBeePL_type ty)=false -> sizeof_type ge.(genv_cenv) ty=sizeof_type env ty ->
  typed_memory_layout env Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
  packet_state_valid m packets -> packet_block_disjoint m packets block ->
  Mem.range_perm m block (Ptrofs.unsigned offset)
    (Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type env ty) Cur Freeable ->
  (align_chunk(transl_bchunk_cchunk chunk)|Ptrofs.unsigned offset) ->
  Ptrofs.unsigned offset+Z.of_nat(length values)*sizeof_type env ty<=Ptrofs.max_unsigned ->
  slot_cells_disjoint cells block (Ptrofs.unsigned offset) (Z.of_nat(length values)*sizeof_type env ty) ->
  exists final after,
    sem_array_init_helper ge m block offset values ty final /\
    typed_memory_layout env Sigma after final /\ memory_locations L after final /\ coherent_layout after /\
    packet_state_valid final packets /\ packet_block_disjoint final packets block /\
    (forall b ofs t ch,cells b ofs t ch -> after b ofs t ch) /\
    (forall index,(index<length values)%nat ->
      after block (Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type env ty)) ty chunk) /\
    (forall b ofs t ch,after b ofs t ch -> cells b ofs t ch \/
      exists index,(index<length values)%nat /\ b=block /\
        ofs=Ptrofs.repr(Ptrofs.unsigned offset+Z.of_nat index*sizeof_type env ty) /\ t=ty /\ ch=chunk).
Proof.
  intros ge env Gamma Sigma L ty chunk values.
  induction values as [|v values IH]; intros m block offset cells packets Hvalues Hmode Hvol Henv
    Hcells Hlocations Hcoherent Hpackets HpacketAway Hfree Halign Hbound Haway.
  - exists m,cells. split; [constructor|].
    split; [exact Hcells|]. split; [exact Hlocations|]. split; [exact Hcoherent|].
    split; [exact Hpackets|]. split; [exact HpacketAway|]. split; [auto|].
    split; [intros index Hindex; simpl in Hindex;lia|]. intros;left;assumption.
  - inversion Hvalues as [|head tail [Hvalue Hlocation] Htail]; subst head tail.
    destruct(scalar_array_stride env ty chunk Hmode) as [Hsize [Hpositive Hstride]].
    assert(HfreeHead:Mem.valid_access m (transl_bchunk_cchunk chunk) block(Ptrofs.unsigned offset) Freeable).
    { split; [|exact Halign]. intros position Hin. apply Hfree; cbn [length];rewrite Nat2Z.inj_succ; nia. }
    destruct(initialize_typed_scalar_array_cell ge env Gamma Sigma L m block offset ty chunk v
      Hvalue Hlocation Hmode Hvol HfreeHead) as [written [Hstore [Hassign [Hcell Hlocated]]]].
    assert(HawayHead:slot_cells_disjoint cells block(Ptrofs.unsigned offset)(size_chunk(transl_bchunk_cchunk chunk))).
    { intros b ofs t ch Hin. destruct(Haway _ _ _ _ Hin) as [Hneq|[Hbefore|Hafter]];
        [left;exact Hneq|right;left;exact Hbefore|right;right;cbn [length] in Hafter;rewrite Nat2Z.inj_succ in Hafter;nia]. }
    destruct(scalar_slot_memory_frame _ _ _ _ _ _ _ _ _ _ _ Hcells Hlocations HawayHead Hstore Hcell Hlocated)
      as [Hcells' Hlocations'].
    assert(Hcoherent':coherent_layout(extend_scalar_layout cells block offset ty chunk))
      by (apply scalar_slot_extension_coherent;assumption).
    destruct(packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hpackets HpacketAway Hassign) as [Hpackets' Hviews].
    assert(HpacketAway':packet_block_disjoint written packets block) by (exact (packet_block_disjoint_frame _ _ _ _ Hpackets Hviews HpacketAway)).
    set(next:=Ptrofs.add offset(Ptrofs.repr(sizeof_type ge.(genv_cenv) ty))).
    assert(Hnext:Ptrofs.unsigned next=Ptrofs.unsigned offset+sizeof_type env ty).
    { assert(Hsmall:0<=sizeof_type env ty<=Ptrofs.max_unsigned).
      { pose proof(Ptrofs.unsigned_range offset). cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia. }
      unfold next,Ptrofs.add. rewrite Henv.
      rewrite (Ptrofs.unsigned_repr (sizeof_type env ty) Hsmall).
      apply Ptrofs.unsigned_repr. pose proof(Ptrofs.unsigned_range offset);
        cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia. }
    destruct(IH written block next (extend_scalar_layout cells block offset ty chunk) packets Htail Hmode Hvol Henv
      Hcells' Hlocations' Hcoherent' Hpackets' HpacketAway') as [final [after [Hhelper [Htyped [Hlocated' [Hcoherent'' [Hpackets'' [HpacketAway'' [Hinc [Hcoverage Horigin]]]]]]]]]].
    + rewrite Hnext. intros position Hin. eapply assignment_preserves_permissions; [exact Hassign|].
      apply Hfree. cbn [length];rewrite Nat2Z.inj_succ;nia.
    + rewrite Hnext. apply Z.divide_add_r;assumption.
    + rewrite Hnext. cbn [length] in Hbound;rewrite Nat2Z.inj_succ in Hbound;nia.
    + rewrite Hnext,Hsize. apply scalar_slot_remaining_disjoint; [pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));nia|].
      replace (size_chunk(transl_bchunk_cchunk chunk)+Z.of_nat(length values)*size_chunk(transl_bchunk_cchunk chunk))
        with (Z.of_nat(length(v::values))*sizeof_type env ty) by (cbn [length];rewrite Nat2Z.inj_succ;nia).
      exact Haway.
    + exists final,after. split.
      * eapply sem_allocate_array_elm; [exact Hassign|exact Hhelper].
      * split; [exact Htyped|]. split; [exact Hlocated'|]. split; [exact Hcoherent''|].
        split; [exact Hpackets''|]. split; [exact HpacketAway''|]. split.
        -- intros;apply Hinc;left;assumption.
        -- split.
           ** intros [|index] Hindex.
              ++ cbn [Z.of_nat]. rewrite Z.mul_0_l,Z.add_0_r,Ptrofs.repr_unsigned. apply Hinc;right;auto.
              ++ replace (Ptrofs.unsigned offset+Z.of_nat(S index)*sizeof_type env ty)
                with (Ptrofs.unsigned next+Z.of_nat index*sizeof_type env ty) by (rewrite Hnext,Nat2Z.inj_succ;ring).
                 apply Hcoverage;simpl in Hindex;lia.
           ** intros b ofs t ch Hin. destruct(Horigin _ _ _ _ Hin) as [[Hold|[Hb [Ho [Ht Hch]]]]|[index [Hi [Hb [Ho [Ht Hch]]]]]].
              ++ left;exact Hold.
              ++ right;exists 0%nat; subst; cbn [Z.of_nat]; rewrite Z.mul_0_l,Z.add_0_r,Ptrofs.repr_unsigned; repeat split;try reflexivity;cbn [length];lia.
              ++ right;exists(S index); subst; repeat split; try (simpl;lia).
                 f_equal;rewrite Hnext,Nat2Z.inj_succ;ring.
Qed.

(* Prefix facts describe only already-written storage.  They leave the remaining
   destination range unclaimed, so the next operation has genuine separation. *)
Definition array_cells_prefix (cells : scalar_layout) dst start : Prop :=
  forall b ofs ty chunk, cells b ofs ty chunk ->
    b<>dst \/ Ptrofs.unsigned ofs+size_chunk(transl_bchunk_cchunk chunk)<=start.

Definition array_packet_prefix m (packets : packet_locations) dst start : Prop :=
  forall b ofs, packets b ofs ->
    (b<>dst \/ Ptrofs.unsigned ofs+packet_descriptor_size<=start) /\
    forall view, packet_descriptor_valid m b ofs view -> packet_block view<>dst.

Lemma array_cells_prefix_separated : forall cells dst start count,
  array_cells_prefix cells dst start -> slot_cells_disjoint cells dst start count.
Proof. intros cells dst start count Hprefix b ofs ty chunk Hin.
  destruct (Hprefix _ _ _ _ Hin); [left|right;left]; assumption. Qed.

Lemma array_packet_prefix_separated : forall m packets dst start count,
  array_packet_prefix m packets dst start -> packet_write_separated m packets dst start count.
Proof.
  intros m packets dst start count Hprefix b ofs Hin.
  destruct(Hprefix _ _ Hin) as [Hdescriptor Hpayload]. split.
  - unfold packet_interval_disjoint; intuition.
  - intros view Hview. right;left; eapply Hpayload;exact Hview.
Qed.

Lemma array_copy_cells_prefix : forall cells src source dst target count,
  0<=target -> 0<=count -> target+count<=Ptrofs.modulus ->
  array_cells_prefix cells dst target ->
  array_cells_prefix(slot_copy_layout cells src source dst target count) dst (target+count).
Proof.
  intros cells src source dst target count Htarget Hcount Hbound Hprefix b ofs ty chunk Hin.
  destruct Hin as [Hold|[Hb [old [delta [Hcell [Hold [Hdelta [Hend Hofs]]]]]]]].
  - destruct(Hprefix _ _ _ _ Hold);[left;assumption|right;lia].
  - subst b ofs. right. rewrite Ptrofs.unsigned_repr.
    + lia.
    + pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)); unfold Ptrofs.max_unsigned;lia.
Qed.

Lemma array_copy_cells_origin : forall seed cells src source dst target count,
  (forall b ofs ty chunk, cells b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) ->
  forall b ofs ty chunk,slot_copy_layout cells src source dst target count b ofs ty chunk ->
    seed b ofs ty chunk \/ b=dst.
Proof. intros seed cells src source dst target count Horigin b ofs ty chunk [Hold|[Hb Hcopy]];
  [apply Horigin;exact Hold|right;exact Hb]. Qed.

Lemma array_copy_source_cells_are_seed : forall (seed cells : scalar_layout) src dst,
  src<>dst ->
  (forall b ofs ty chunk,cells b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) ->
  forall ofs ty chunk,cells src ofs ty chunk -> seed src ofs ty chunk.
Proof. intros seed cells src dst Hneq Horigin ofs ty chunk Hin.
  destruct(Horigin _ _ _ _ Hin);congruence. Qed.

Lemma array_copy_packet_prefix : forall env root packets m final src source dst target bytes,
  0<=source -> source+sizeof_type env root<=Ptrofs.modulus ->
  0<=target -> target+sizeof_type env root<=Ptrofs.modulus ->
  0<=sizeof_type env root ->
  packet_state_valid m packets -> array_packet_prefix m packets dst target ->
  (forall delta,object_path env root delta Bytes -> packets src(Ptrofs.repr(source+delta))) ->
  (forall delta,object_path env root delta Bytes -> (align_chunk Mptr|target+delta)) ->
  Mem.loadbytes m src source (sizeof_type env root)=Some bytes ->
  Mem.storebytes m dst target bytes=Some final ->
  array_packet_prefix final(slot_copy_packets env packets root dst target) dst (target+sizeof_type env root).
Proof.
  intros env root packets m final src source dst target bytes Hsource HsourceEnd Htarget HtargetEnd Hsize
    Hvalid Hprefix Hcovered Haligned Hread Hstore b ofs Hin.
  destruct Hin as [Hold|[Hb [delta [Hpath Hofs]]]].
  - destruct(Hprefix _ _ Hold) as [Hposition Hpayload]. split.
    + destruct Hposition;[left;assumption|right;lia].
    + intros view Hview. destruct(Hvalid _ _ Hold) as [_ [oldview [contents [Holdview Hrest]]]].
      assert(Holdview' : packet_descriptor_valid final b ofs oldview).
      { eapply packet_descriptor_storebytes_disjoint;[exact Hstore| |exact Holdview]. intuition. }
      assert(view=oldview) by (eapply packet_descriptor_view_unique;eauto).
      subst view;apply Hpayload;exact Holdview.
  - subst b ofs. pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [_ Hend]].
    change(delta+packet_descriptor_size<=sizeof_type env root) in Hend.
    split.
    + right. rewrite Ptrofs.unsigned_repr;[lia|].
      pose proof packet_descriptor_size_positive; unfold Ptrofs.max_unsigned;lia.
    + intros view Hview. pose proof(Hcovered _ Hpath) as Hregistered.
      destruct(Hvalid _ _ Hregistered) as [_ [oldview [contents [Holdview Hrest]]]].
      assert(Hcopy : packet_descriptor_valid final dst (Ptrofs.repr(target+delta)) oldview).
      { eapply (slot_copied_descriptor env root m final src source dst target bytes delta oldview); eauto. }
      assert(view=oldview) by(eapply packet_descriptor_view_unique;eauto).
      subst view. apply (proj2(Hprefix _ _ Hregistered)); exact Holdview.
Qed.

Definition array_copy_leaf_alignment env root start count : Prop :=
  forall index,(index<count)%nat ->
  (forall delta ty chunk,scalar_object_leaf env root delta ty chunk ->
    (align_chunk(transl_bchunk_cchunk chunk)|start+Z.of_nat index*sizeof_type env root+delta)) /\
  (forall delta,object_path env root delta Bytes ->
    (align_chunk Mptr|start+Z.of_nat index*sizeof_type env root+delta)).

Inductive array_copy_source env (seed : scalar_layout) (packets : packet_locations)
    m dst root (v : value) : Prop :=
| array_copy_source_intro : forall src source,
  v=Vloc src source -> src<>dst -> Mem.valid_block m src ->
  Ptrofs.unsigned source+sizeof_type env root<=Ptrofs.modulus ->
  ((if is_bytes root then align_chunk Mptr else
    alignof_blockcopy(bcomposite_composite_env env)(transBeePL_type root))|Ptrofs.unsigned source) ->
  Mem.range_perm m src(Ptrofs.unsigned source)(Ptrofs.unsigned source+sizeof_type env root) Cur Readable ->
  (forall delta ty chunk,scalar_object_leaf env root delta ty chunk ->
    exists stored,seed src(Ptrofs.repr(Ptrofs.unsigned source+delta)) ty stored /\
      transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) ->
  (0<sizeof_type env root -> forall delta child,object_path env root delta child ->
    scalar_object_region_coherent env seed src(Ptrofs.unsigned source+delta) child) ->
  (forall delta,object_path env root delta Bytes ->
    packets src(Ptrofs.repr(Ptrofs.unsigned source+delta))) ->
  array_copy_source env seed packets m dst root v.

Lemma array_copy_sources_assignment_frame : forall ge env seed packets m dst root values target assigned final result,
  Forall(array_copy_source env seed packets m dst root) values ->
  assign_addr ge root m dst target Full assigned final result ->
  Forall(array_copy_source env seed packets final dst root) values.
Proof.
  intros ge env seed packets m dst root values target assigned final result Hsources Hassign.
  eapply Forall_impl;[|exact Hsources]. intros value Hsource.
  destruct Hsource as [src source Hv Hapart Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
  eapply array_copy_source_intro with (src:=src)(source:=source);try assumption.
  - eapply assignment_preserves_valid_blocks; eauto.
  - intros position Hposition. eapply assignment_preserves_permissions;[exact Hassign|apply Hread;exact Hposition].
Qed.

Lemma array_current_source_regions : forall env seed cells src source dst root,
  src<>dst ->
  (forall b ofs ty chunk,cells b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) ->
  (forall delta child,object_path env root delta child ->
    scalar_object_region_coherent env seed src(source+delta) child) ->
  forall delta child,object_path env root delta child ->
    scalar_object_region_coherent env cells src(source+delta) child.
Proof.
  intros env seed cells src source dst root Hapart Horigin Hregions delta child Hpath b ofs ty chunk Hin.
  destruct(Horigin _ _ _ _ Hin) as [Hold|Hb].
  - eapply Hregions;eauto.
  - left;left;congruence.
Qed.

Lemma array_current_source_alignment : forall env seed cells src source dst target root,
  src<>dst ->
  (forall b ofs ty chunk,cells b ofs ty chunk -> seed b ofs ty chunk \/ b=dst) ->
  scalar_object_region_coherent env seed src source root ->
  (forall delta ty chunk,scalar_object_leaf env root delta ty chunk ->
    (align_chunk(transl_bchunk_cchunk chunk)|target+delta)) ->
  slot_copy_alignment cells src source target(sizeof_type env root).
Proof.
  intros env seed cells src source dst target root Hapart Horigin Hregion Halign old ty chunk delta Hcell Hoffset Hd Hend.
  assert(Hseed:seed src old ty chunk) by(eapply array_copy_source_cells_are_seed;eauto).
  destruct(Hregion _ _ _ _ Hseed) as [[Hneq|[Hbefore|Hafter]]|[relative [Hleaf [Hb Hrelative]]]].
  - contradiction.
  - pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia.
  - pose proof(size_chunk_pos(transl_bchunk_cchunk chunk));lia.
  - replace delta with relative by lia;eapply Halign;exact Hleaf.
Qed.
