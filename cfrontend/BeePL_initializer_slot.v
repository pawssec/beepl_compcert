(* Initialization of a destination subrange. Earlier initialized slots remain
   live in the same block; only the still-uninitialized target interval must
   be disjoint. Parent aggregate coverage is assembled after all slots finish. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_scalar_parameters BeePL_copy_bytes BeePL_copy_cells.
Require Import BeePL_object_paths BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy.
Import ListNotations.
Local Open Scope Z_scope.

Definition slot_cells_disjoint (cells : scalar_layout) dst start count : Prop :=
  forall b ofs ty chunk, cells b ofs ty chunk ->
    b <> dst \/ Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= start \/
    start + count <= Ptrofs.unsigned ofs.

Theorem initialize_scalar_slot : forall ge cenv Gamma Sigma L cells packets m dst target ty v,
  scalar_parameter_type ty -> type_expr cenv Gamma Sigma (Val v ty) [] ty ->
  value_locations L v ty ->
  typed_memory_layout cenv Sigma cells m -> memory_locations L cells m ->
  packet_state_valid m packets ->
  Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty)) dst (Ptrofs.unsigned target) Freeable ->
  slot_cells_disjoint cells dst (Ptrofs.unsigned target)
    (size_chunk (transl_bchunk_cchunk (scalar_parameter_chunk ty))) ->
  packet_write_separated m packets dst (Ptrofs.unsigned target)
    (size_chunk (transl_bchunk_cchunk (scalar_parameter_chunk ty))) ->
  exists final,
    Mem.store (transl_bchunk_cchunk (scalar_parameter_chunk ty)) m dst (Ptrofs.unsigned target)
      (trans_bvalue_cvalue v) = Some final /\
    assign_addr ge ty m dst target Full v final v /\
    typed_memory_layout cenv Sigma (extend_scalar_layout cells dst target ty (scalar_parameter_chunk ty)) final /\
    memory_locations L (extend_scalar_layout cells dst target ty (scalar_parameter_chunk ty)) final /\
    packet_state_valid final packets.
Proof.
  intros ge cenv Gamma Sigma L cells packets m dst target ty v
    Hscalar Hvalue Hlocation Hcells Hlocations Hpackets Hpermission Hdisjoint Hseparated.
  destruct (initialize_scalar_parameter ge cenv Gamma Sigma L m dst target ty v
    Hscalar Hvalue Hlocation Hpermission) as [final [Hstore [Hassign [Hcell Hlocated]]]].
  assert (Hold : forall b ofs t chunk, cells b ofs t chunk ->
    typed_memory_cell cenv Sigma final b ofs t chunk /\
    forall value, deref_addr t final b ofs Full value -> value_locations L value t).
  { intros b ofs t chunk Hentry. pose proof (Hdisjoint _ _ _ _ Hentry) as Hapart.
    split.
    - eapply typed_memory_cell_store_disjoint; [apply Hcells; exact Hentry|exact Hstore|tauto].
    - intros value Hread.
      destruct (Hcells _ _ _ _ Hentry) as [Hmode Hvol Hperm [cv [old [Hload [Hdecode Htyped]]]]].
      assert (HreadOld : deref_addr t final b ofs Full old).
      { eapply deref_addr_value; eauto. simpl.
        rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload|tauto]. }
      assert (value=old) by (eapply deref_full_deterministic; eauto). subst value.
      eapply Hlocations; [exact Hentry|]. eapply deref_addr_value; eauto. }
  exists final. split; [exact Hstore|]. split; [exact Hassign|]. split.
  - intros b ofs t chunk [Hentry|[Hb [Ho [Ht Hchunk]]]]; [apply (proj1 (Hold _ _ _ _ Hentry))|].
    subst; exact Hcell.
  - split.
    + intros b ofs t chunk [Hentry|[Hb [Ho [Ht Hchunk]]]] value Hread.
      * eapply (proj2 (Hold _ _ _ _ Hentry)); exact Hread.
      * subst; eapply Hlocated; exact Hread.
    + eapply packet_state_store_preserved; eauto.
Qed.

Definition slot_copy_layout (cells : scalar_layout) src source dst target count : scalar_layout :=
  fun b ofs ty chunk => cells b ofs ty chunk \/
    (b = dst /\ exists old delta,
      cells src old ty chunk /\ Ptrofs.unsigned old = source + delta /\
      0 <= delta /\ delta + size_chunk (transl_bchunk_cchunk chunk) <= count /\
      ofs = Ptrofs.repr (target + delta)).

Definition slot_copy_alignment (cells : scalar_layout) src source target count : Prop :=
  forall old ty chunk delta,
    cells src old ty chunk -> Ptrofs.unsigned old = source + delta ->
    0 <= delta -> delta + size_chunk (transl_bchunk_cchunk chunk) <= count ->
    (align_chunk (transl_bchunk_cchunk chunk) | target + delta).

Lemma slot_copy_layout_plan : forall cells src source dst target count,
  0 <= target -> target + count <= Ptrofs.modulus ->
  slot_cells_disjoint cells dst target count -> slot_copy_alignment cells src source target count ->
  scalar_copy_plan cells (slot_copy_layout cells src source dst target count) src source dst target count.
Proof.
  intros cells src source dst target count Htarget Hbound Hdisjoint Halign b ofs ty chunk [Hold|[Hb [old [delta [Hcell [Hoffset [Hdelta [Hinside Heq]]]]]]]].
  - left; split; [exact Hold|eapply Hdisjoint; exact Hold].
  - subst b ofs. right; split; [reflexivity|]. exists delta,old.
    pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
    assert (Hrepr : Ptrofs.unsigned (Ptrofs.repr (target+delta)) = target+delta)
      by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
    repeat split; try assumption; rewrite Hrepr; eauto.
Qed.

Lemma slot_copy_covers_source_leaf : forall cells src source dst target count delta ty chunk,
  cells src (Ptrofs.repr (source+delta)) ty chunk ->
  Ptrofs.unsigned (Ptrofs.repr (source+delta)) = source+delta ->
  0 <= delta -> delta + size_chunk (transl_bchunk_cchunk chunk) <= count ->
  slot_copy_layout cells src source dst target count dst (Ptrofs.repr (target+delta)) ty chunk.
Proof. intros; right; split; [reflexivity|]. do 2 eexists; repeat split; eauto. Qed.

Definition slot_copy_packets cenv (packets : packet_locations) root dst target : packet_locations :=
  fun b ofs => packets b ofs \/
    (b=dst /\ exists delta, object_path cenv root delta Bytes /\ ofs=Ptrofs.repr (target+delta)).

Lemma slot_copy_packet_leaf_registered : forall cenv packets root dst target delta,
  object_path cenv root delta Bytes ->
  slot_copy_packets cenv packets root dst target dst (Ptrofs.repr (target+delta)).
Proof. intros; right; split; [reflexivity|]. exists delta; auto. Qed.

Lemma slot_copied_descriptor : forall cenv root m final src source dst target bytes delta view,
  0 <= source -> source + sizeof_type cenv root <= Ptrofs.modulus ->
  0 <= target -> target + sizeof_type cenv root <= Ptrofs.modulus ->
  object_path cenv root delta Bytes -> (align_chunk Mptr | target+delta) ->
  packet_descriptor_valid m src (Ptrofs.repr (source+delta)) view ->
  Mem.loadbytes m src source (sizeof_type cenv root) = Some bytes ->
  Mem.storebytes m dst target bytes = Some final ->
  packet_descriptor_valid final dst (Ptrofs.repr (target+delta)) view.
Proof.
  intros cenv root m final src source dst target bytes delta view Hsource HsourceEnd Htarget HtargetEnd
    Hpath Halign [Hfirst [Hlast Hview]] Hread Hstore.
  pose proof (object_path_bounds _ _ _ _ Hpath) as [Hd [_ Hinside]].
  change (delta+packet_descriptor_size<=sizeof_type cenv root) in Hinside.
  pose proof packet_descriptor_size_positive.
  assert (Hs : Ptrofs.unsigned(Ptrofs.repr(source+delta))=source+delta)
    by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
  assert (Ht : Ptrofs.unsigned(Ptrofs.repr(target+delta))=target+delta)
    by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
  pose proof (size_chunk_pos Mptr) as Hpointer.
  rewrite Hs in Hfirst,Hlast. unfold packet_descriptor_valid; rewrite Ht.
  split.
  - eapply copied_bytes_scalar_load; eauto; unfold packet_descriptor_size in Hinside; lia.
  - split.
    + replace (target+delta+size_chunk Mptr) with (target+(delta+size_chunk Mptr)) by lia.
      eapply copied_bytes_scalar_load with (delta:=delta+size_chunk Mptr); eauto;
        try (unfold packet_descriptor_size in Hinside; pose proof(size_chunk_pos Mptr); lia).
      * replace (target+(delta+size_chunk Mptr)) with (target+delta+size_chunk Mptr) by lia.
        apply Z.divide_add_r; [exact Halign|apply pointer_slot_alignment].
      * replace (source+(delta+size_chunk Mptr)) with (source+delta+size_chunk Mptr) by lia; exact Hlast.
    + eapply packet_view_valid_frame; [exact Hview| |].
      * intros; eapply Mem.storebytes_valid_block_1; eauto.
      * intros; eapply Mem.perm_storebytes_1; eauto.
Qed.

Theorem slot_copy_packet_state : forall cenv root packets m final src source dst target bytes,
  0 <= sizeof_type cenv root -> 0 <= source -> source+sizeof_type cenv root <= Ptrofs.modulus ->
  0 <= target -> target+sizeof_type cenv root <= Ptrofs.modulus ->
  packet_state_valid m packets ->
  (forall delta, object_path cenv root delta Bytes -> packets src (Ptrofs.repr(source+delta))) ->
  (forall delta, object_path cenv root delta Bytes -> (align_chunk Mptr | target+delta)) ->
  packet_write_separated m packets dst target (sizeof_type cenv root) ->
  Mem.loadbytes m src source (sizeof_type cenv root) = Some bytes ->
  Mem.storebytes m dst target bytes = Some final ->
  packet_state_valid final (slot_copy_packets cenv packets root dst target).
Proof.
  intros cenv root packets m final src source dst target bytes Hsize Hsource HsourceEnd Htarget HtargetEnd
    Hpackets Hcoverage Halign Hseparated Hread Hstore.
  assert (Hlength : Z.of_nat(length bytes)=sizeof_type cenv root)
    by (rewrite (Mem.loadbytes_length _ _ _ _ _ Hread),Z2Nat.id; auto).
  assert (Hold : packet_state_valid final packets).
  { eapply packet_state_storebytes_preserved; [exact Hpackets|rewrite Hlength; exact Hseparated|exact Hstore]. }
  intros b ofs [Hentry|[Hb [delta [Hpath Hofs]]]]; [apply Hold; exact Hentry|].
  subst b ofs. pose proof(Hcoverage _ Hpath) as Hentry.
  destruct (Hpackets _ _ Hentry) as [Hbound [view [contents [Hdescriptor [Hcontents Hinit]]]]].
  pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [_ Hinside]].
  change (delta+packet_descriptor_size<=sizeof_type cenv root) in Hinside.
  pose proof packet_descriptor_size_positive.
  assert (Ht : Ptrofs.unsigned(Ptrofs.repr(target+delta))=target+delta)
    by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
  split; [rewrite Ht; lia|]. exists view,contents. split.
  - eapply (slot_copied_descriptor cenv root m final src source dst target bytes delta view); eauto.
  - split; [|exact Hinit].
    pose proof (proj2 (Hseparated _ _ Hentry) view Hdescriptor) as Haway.
    unfold packet_interval_disjoint in Haway.
    destruct Haway as [Hzero|Haway].
    + rewrite Hzero in *. rewrite Mem.loadbytes_empty in * by lia; exact Hcontents.
    + pose proof (proj1 (proj2 (proj2 Hdescriptor))) as Horder.
      rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore); [exact Hcontents|lia|]. rewrite Hlength; exact Haway.
Qed.

Record initializer_copy_ready (ge : genv) (m : Mem.mem) (root : type)
    (src : Values.block) (source : ptrofs) (dst : Values.block) (target : ptrofs) : Prop := {
  slot_copy_kind : is_aggregate_type root = true \/ root = Bytes;
  slot_copy_size : 0 <= sizeof_type ge.(genv_cenv) root;
  slot_source_valid : Mem.valid_block m src;
  slot_target_valid : Mem.valid_block m dst;
  slot_source_bound : Ptrofs.unsigned source + sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus;
  slot_target_bound : Ptrofs.unsigned target + sizeof_type ge.(genv_cenv) root <= Ptrofs.modulus;
  slot_source_alignment : ((if is_bytes root then align_chunk Mptr else
    alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type root)) | Ptrofs.unsigned source);
  slot_target_alignment : ((if is_bytes root then align_chunk Mptr else
    alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv)) (transBeePL_type root)) | Ptrofs.unsigned target);
  slot_source_target_apart : src <> dst \/ Ptrofs.unsigned source = Ptrofs.unsigned target \/
    Ptrofs.unsigned source + sizeof_type ge.(genv_cenv) root <= Ptrofs.unsigned target \/
    Ptrofs.unsigned target + sizeof_type ge.(genv_cenv) root <= Ptrofs.unsigned source;
  slot_source_readable : Mem.range_perm m src (Ptrofs.unsigned source)
    (Ptrofs.unsigned source+sizeof_type ge.(genv_cenv) root) Cur Readable;
  slot_target_freeable : Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target+sizeof_type ge.(genv_cenv) root) Cur Freeable
}.

Theorem initialize_copy_slot : forall ge Sigma L cells packets m root src source dst target,
  initializer_copy_ready ge m root src source dst target ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m ->
  slot_cells_disjoint cells dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root) ->
  slot_copy_alignment cells src (Ptrofs.unsigned source) (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root) ->
  packet_state_valid m packets ->
  (forall delta, object_path ge.(genv_cenv) root delta Bytes ->
    packets src (Ptrofs.repr(Ptrofs.unsigned source+delta))) ->
  (forall delta, object_path ge.(genv_cenv) root delta Bytes ->
    (align_chunk Mptr | Ptrofs.unsigned target+delta)) ->
  packet_write_separated m packets dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root) ->
  exists final bytes,
    Mem.loadbytes m src (Ptrofs.unsigned source) (sizeof_type ge.(genv_cenv) root)=Some bytes /\
    Mem.storebytes m dst (Ptrofs.unsigned target) bytes=Some final /\
    assign_addr ge root m dst target Full (Vloc src source) final (Vloc src source) /\
    typed_memory_layout ge.(genv_cenv) Sigma
      (slot_copy_layout cells src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root)) final /\
    memory_locations L
      (slot_copy_layout cells src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root)) final /\
    packet_state_valid final (slot_copy_packets ge.(genv_cenv) packets root dst (Ptrofs.unsigned target)).
Proof.
  intros ge Sigma L cells packets m root src source dst target
    [Hkind Hsize Hsrc Hdst HsrcBound HdstBound HsrcAlign HdstAlign Hapart Hread Hfree]
    Hcells Hlocations Hdisjoint Halign Hpackets Hcoverage HpacketAlign Hseparated.
  destruct (Mem.range_perm_loadbytes m src (Ptrofs.unsigned source) (sizeof_type ge.(genv_cenv) root) Hread)
    as [bytes Hbytes].
  assert (Hlength : Z.of_nat(length bytes)=sizeof_type ge.(genv_cenv) root)
    by (rewrite (Mem.loadbytes_length _ _ _ _ _ Hbytes),Z2Nat.id; auto).
  assert (Hwrite : Mem.range_perm m dst (Ptrofs.unsigned target)
    (Ptrofs.unsigned target+Z.of_nat(length bytes)) Cur Writable).
  { rewrite Hlength; intros ofs Hin; eapply Mem.perm_implies; [apply Hfree; exact Hin|constructor]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ Hwrite) as [final Hstore].
  assert (Hassign : assign_addr ge root m dst target Full (Vloc src source) final (Vloc src source)).
  { destruct Hkind as [Haggregate|HbytesKind].
    - assert (Hnotbytes : is_bytes root=false) by (destruct root; simpl in *; congruence).
      rewrite Hnotbytes in HsrcAlign,HdstAlign. eapply assign_addr_copy; eauto.
    - subst root. eapply assign_addr_bytes_copy; eauto. }
  destruct (typed_located_layout_copy ge.(genv_cenv) Sigma L cells
    (slot_copy_layout cells src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root))
    m final src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root) bytes
    Hsize Hbytes Hstore Hfree Hcells Hlocations
    ltac:(apply slot_copy_layout_plan; auto; pose proof(Ptrofs.unsigned_range target); lia)) as [Hcells' Hlocations'].
  exists final,bytes. split; [exact Hbytes|]. split; [exact Hstore|]. split; [exact Hassign|].
  split; [exact Hcells'|]. split; [exact Hlocations'|].
  eapply (slot_copy_packet_state ge.(genv_cenv) root packets m final src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) bytes); eauto; pose proof(Ptrofs.unsigned_range source); pose proof(Ptrofs.unsigned_range target); lia.
Qed.

Lemma slot_copy_packets_typed : forall cenv Sigma packets root dst target,
  packet_state_typed cenv Sigma packets ->
  object_type_at cenv Sigma dst target root ->
  0 <= target -> target+sizeof_type cenv root <= Ptrofs.modulus ->
  packet_state_typed cenv Sigma (slot_copy_packets cenv packets root dst target).
Proof.
  intros cenv Sigma packets root dst target Htyped Hroot Htarget Hbound b ofs [Hold|[Hb [delta [Hpath Hofs]]]];
    [apply Htyped; exact Hold|]. subst b ofs.
  pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [_ Hinside]].
  change (delta+packet_descriptor_size<=sizeof_type cenv root) in Hinside.
  pose proof packet_descriptor_size_positive.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  eapply object_path_typing; eauto.
Qed.

Theorem initialize_unit_array_slot : forall ge m block offset values final,
  sem_array_init_helper ge m block offset values Utype final ->
  sem_array_init_helper ge m block offset (Vunit::values) Utype final.
Proof. intros; apply sem_allocate_array_unit; assumption. Qed.

Print Assumptions initialize_scalar_slot.
Print Assumptions initialize_copy_slot.
Print Assumptions slot_copy_packets_typed.

Require Import BeePL_layout_coherence.

Theorem slot_copy_layout_coherent : forall cells src source dst target count,
  coherent_layout cells -> slot_cells_disjoint cells dst target count ->
  0 <= target -> target+count <= Ptrofs.modulus ->
  coherent_layout (slot_copy_layout cells src source dst target count).
Proof.
  intros cells src source dst target count Hcoherent Haway Htarget Hend b ofs ty chunk Hcell old off t ch Hold.
  destruct Hcell as [Hcell|[Hb [origin [delta [Hsource [Hofs [Hdelta [Hlimit Heq]]]]]]]];
    destruct Hold as [Hold|[Hob [origin' [delta' [Hsource' [Hoff [Hdelta' [Hlimit' Heq']]]]]]]].
  - eapply Hcoherent; eauto.
  - subst old off. pose proof(size_chunk_pos(transl_bchunk_cchunk ch)).
    assert (Hr : 0<=target+delta'<=Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
    destruct (Haway _ _ _ _ Hcell) as [Hneq|[Hbefore|Hafter]].
    + right; left; congruence.
    + right; right; left; rewrite Ptrofs.unsigned_repr by exact Hr; lia.
    + right; right; right; rewrite Ptrofs.unsigned_repr by exact Hr; lia.
  - subst b ofs. pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
    assert (Hr : 0<=target+delta<=Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
    destruct (Haway _ _ _ _ Hold) as [Hneq|[Hbefore|Hafter]].
    + right; left; exact Hneq.
    + right; right; right; rewrite Ptrofs.unsigned_repr by exact Hr; lia.
    + right; right; left; rewrite Ptrofs.unsigned_repr by exact Hr; lia.
  - subst b old ofs off.
    pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
    pose proof(size_chunk_pos(transl_bchunk_cchunk ch)).
    assert (Hr : 0<=target+delta<=Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
    assert (Hr' : 0<=target+delta'<=Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
    destruct (Hcoherent _ _ _ _ Hsource _ _ _ _ Hsource')
      as [[Hb [Hoffset [Hty Hchunk]]]|[Hneq|[Hafter|Hbefore]]].
    + subst origin' t ch. assert (delta'=delta) by lia. subst delta'; left; auto.
    + contradiction.
    + right; right; left; rewrite !Ptrofs.unsigned_repr by assumption; lia.
    + right; right; right; rewrite !Ptrofs.unsigned_repr by assumption; lia.
Qed.

Theorem slot_copy_scalar_leaf_coverage : forall cenv cells src source dst target root,
  0 <= source -> source+sizeof_type cenv root <= Ptrofs.modulus ->
  (forall delta ty chunk, scalar_object_leaf cenv root delta ty chunk ->
    exists stored, cells src (Ptrofs.repr(source+delta)) ty stored /\
      transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) ->
  forall delta ty chunk, scalar_object_leaf cenv root delta ty chunk ->
  exists stored, slot_copy_layout cells src source dst target (sizeof_type cenv root)
    dst (Ptrofs.repr(target+delta)) ty stored /\
    transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Proof.
  intros cenv cells src source dst target root Hsource Hend Hcoverage delta ty chunk Hleaf.
  destruct (Hcoverage _ _ _ Hleaf) as [stored [Hcell Heq]].
  pose proof(scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as [Hdelta [Hsize Hinside]].
  exists stored; split; [|exact Heq]. apply slot_copy_covers_source_leaf; auto.
  - apply Ptrofs.unsigned_repr. pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)); unfold Ptrofs.max_unsigned; lia.
  - rewrite Heq; exact Hinside.
Qed.

Print Assumptions slot_copy_layout_coherent.
Print Assumptions slot_copy_scalar_leaf_coverage.

Require Import BeePL_scalar_object_layout.

Theorem slot_copy_declared_regions : forall cenv cells src source dst target root,
  0 <= target -> target+sizeof_type cenv root <= Ptrofs.modulus ->
  slot_cells_disjoint cells dst target (sizeof_type cenv root) ->
  (forall delta child, object_path cenv root delta child ->
    scalar_object_region_coherent cenv cells src (source+delta) child) ->
  forall delta child, object_path cenv root delta child ->
    scalar_object_region_coherent cenv
      (slot_copy_layout cells src source dst target (sizeof_type cenv root)) dst (target+delta) child.
Proof.
  intros cenv cells src source dst target root Htarget Hbound Hdisjoint Hsource delta child Hpath b ofs ty chunk Hentry.
  pose proof(object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hchild Hinside]].
  destruct Hentry as [Hold|[Hb [old [shift [Hcell [Hoffset [Hshift [Hlimit Hofs]]]]]]]].
  - left. destruct (Hdisjoint _ _ _ _ Hold) as [Hneq|[Hbefore|Hafter]]; [auto|right;left;lia|right;right;lia].
  - subst b ofs. pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)).
    assert (Hrepr : Ptrofs.unsigned(Ptrofs.repr(target+shift))=target+shift)
      by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
    destruct (Hsource _ _ Hpath _ _ _ _ Hcell) as [[Hneq|[Hbefore|Hafter]]|[leaf [Hleaf [Hb HleafOffset]]]].
    + contradiction.
    + left; right; left; rewrite Hrepr; lia.
    + left; right; right; rewrite Hrepr; lia.
    + right; exists leaf; split; [exact Hleaf|]. split; [reflexivity|]. rewrite Hrepr; lia.
Qed.

Print Assumptions slot_copy_declared_regions.

Require Import BeePL_option_representation BeePL_substitution_proofs.

Lemma direct_function_pointer_value_uninhabited : forall cenv Gamma Sigma v args effects result variadic ef,
  ~ type_expr cenv Gamma Sigma (Val v (Ptrtype (Fptype args effects result variadic))) ef
    (Ptrtype (Fptype args effects result variadic)).
Proof. intros * H; inversion H. Qed.

Lemma optional_function_pointer_value_is_none : forall cenv Gamma Sigma v args effects result variadic ef,
  type_expr cenv Gamma Sigma (Val v (Ptrtype (Otype (Fptype args effects result variadic)))) ef
    (Ptrtype (Otype (Fptype args effects result variadic))) -> v=Voption None.
Proof.
  intros * H; inversion H; subst.
  destruct o as [payload|]; [|reflexivity].
  exfalso; eapply direct_function_pointer_value_uninhabited; eauto.
Qed.

Lemma null_function_option_normalizes : forall args effects result variadic,
  decode_memory_value (Ptrtype (Otype (Fptype args effects result variadic)))
    (Values.Val.load_result Mptr (trans_bvalue_cvalue (Voption None))) = OK (Voption None).
Proof. intros; apply option_memory_roundtrip; [reflexivity|exact I]. Qed.

Theorem initialize_null_function_option_cell : forall ge cenv Sigma L m dst target args effects result variadic,
  Mem.valid_access m Mptr dst (Ptrofs.unsigned target) Freeable ->
  exists final,
    Mem.store Mptr m dst (Ptrofs.unsigned target) (trans_bvalue_cvalue (Voption None))=Some final /\
    assign_addr ge (Ptrtype (Otype (Fptype args effects result variadic))) m dst target Full
      (Voption None) final (Voption None) /\
    typed_memory_cell cenv Sigma final dst target
      (Ptrtype (Otype (Fptype args effects result variadic))) option_pointer_chunk /\
    (forall loaded, deref_addr (Ptrtype (Otype (Fptype args effects result variadic))) final dst target Full loaded ->
      value_locations L loaded (Ptrtype (Otype (Fptype args effects result variadic)))).
Proof.
  intros ge cenv Sigma L m dst target args effects result variadic Haccess.
  destruct (Mem.valid_access_store m Mptr dst (Ptrofs.unsigned target)
    (trans_bvalue_cvalue (Voption None)) ltac:(eapply Mem.valid_access_implies; [exact Haccess|constructor]))
    as [final Hstore].
  assert (Hread : deref_addr (Ptrtype (Otype (Fptype args effects result variadic))) final dst target Full (Voption None)).
  { eapply deref_addr_value with (chunk:=option_pointer_chunk).
    - simpl; rewrite option_pointer_chunk_translation; reflexivity.
    - reflexivity.
    - simpl; rewrite option_pointer_chunk_translation; eapply Mem.load_store_same; exact Hstore.
    - apply null_function_option_normalizes. }
  exists final; split; [exact Hstore|]. split.
  - eapply assign_addr_option; eauto; reflexivity || exact I.
  - split.
    + constructor.
      * simpl; rewrite option_pointer_chunk_translation; reflexivity.
      * reflexivity.
      * rewrite option_pointer_chunk_translation; eapply Mem.store_valid_access_1; eauto.
      * exists (Values.Val.load_result Mptr (trans_bvalue_cvalue (Voption None))), (Voption None).
        split; [rewrite option_pointer_chunk_translation; eapply Mem.load_store_same; exact Hstore|].
        split; [apply null_function_option_normalizes|]. constructor; [reflexivity|intros v Hbad; discriminate Hbad].
    + intros loaded Hr. assert (loaded=Voption None) by (eapply deref_full_deterministic; eauto).
      subst; exact I.
Qed.

Theorem initialize_null_function_option_slot : forall ge cenv Sigma L cells packets m dst target args effects result variadic,
  typed_memory_layout cenv Sigma cells m -> memory_locations L cells m ->
  packet_state_valid m packets -> Mem.valid_access m Mptr dst (Ptrofs.unsigned target) Freeable ->
  slot_cells_disjoint cells dst (Ptrofs.unsigned target) (size_chunk Mptr) ->
  packet_write_separated m packets dst (Ptrofs.unsigned target) (size_chunk Mptr) ->
  exists final,
    assign_addr ge (Ptrtype (Otype (Fptype args effects result variadic))) m dst target Full
      (Voption None) final (Voption None) /\
    typed_memory_layout cenv Sigma
      (extend_scalar_layout cells dst target (Ptrtype (Otype (Fptype args effects result variadic))) option_pointer_chunk) final /\
    memory_locations L
      (extend_scalar_layout cells dst target (Ptrtype (Otype (Fptype args effects result variadic))) option_pointer_chunk) final /\
    packet_state_valid final packets.
Proof.
  intros ge cenv Sigma L cells packets m dst target args effects result variadic
    Hcells Hlocations Hpackets Hpermission Hdisjoint Hseparated.
  destruct (initialize_null_function_option_cell ge cenv Sigma L m dst target args effects result variadic Hpermission)
    as [final [Hstore [Hassign [Hcell Hlocated]]]].
  assert (Hold : forall b ofs t chunk, cells b ofs t chunk ->
    typed_memory_cell cenv Sigma final b ofs t chunk /\
    forall value, deref_addr t final b ofs Full value -> value_locations L value t).
  { intros b ofs t chunk Hentry. pose proof (Hdisjoint _ _ _ _ Hentry) as Hapart.
    split.
    - eapply typed_memory_cell_store_disjoint; [apply Hcells; exact Hentry|exact Hstore|tauto].
    - intros value Hread.
      destruct (Hcells _ _ _ _ Hentry) as [Hmode Hvol Hperm [cv [old [Hload [Hdecode Htyped]]]]].
      assert (HreadOld : deref_addr t final b ofs Full old).
      { eapply deref_addr_value; eauto. simpl.
        rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore); [exact Hload|tauto]. }
      assert (value=old) by (eapply deref_full_deterministic; eauto). subst value.
      eapply Hlocations; [exact Hentry|]. eapply deref_addr_value; eauto. }
  exists final. split; [exact Hassign|]. split.
  - intros b ofs t chunk [Hentry|[Hb [Ho [Ht Hchunk]]]]; [apply (proj1 (Hold _ _ _ _ Hentry))|].
    subst; exact Hcell.
  - split.
    + intros b ofs t chunk [Hentry|[Hb [Ho [Ht Hchunk]]]] value Hread.
      * eapply (proj2 (Hold _ _ _ _ Hentry)); exact Hread.
      * subst; eapply Hlocated; exact Hread.
    + eapply packet_state_store_preserved; eauto.
Qed.

Print Assumptions initialize_null_function_option_slot.

Lemma typed_scalar_slot_cases : forall cenv Gamma Sigma ty v chunk,
  type_expr cenv Gamma Sigma (Val v ty) [] ty ->
  access_mode_type ty = By_value chunk -> type_is_volatile (transBeePL_type ty) = false ->
  scalar_parameter_type ty \/ exists args effects result variadic,
    ty = Ptrtype (Otype (Fptype args effects result variadic)) /\ v=Voption None.
Proof.
  intros cenv Gamma Sigma ty v chunk Htyped Hmode Hvolatile.
  destruct ty; try discriminate Hmode.
  - left; split; [left; eauto|exact Hvolatile].
  - destruct p as [bt a|inner|args effects result variadic].
    + left; split; [right; left; eauto|exact Hvolatile].
    + destruct inner as [bt a|nested|args effects result variadic].
      * left; split; [right; right; eauto|exact Hvolatile].
      * inversion Htyped; subst; discriminate.
      * right; exists args,effects,result,variadic; split; [reflexivity|].
        eapply optional_function_pointer_value_is_none; exact Htyped.
    + exfalso; eapply direct_function_pointer_value_uninhabited; exact Htyped.
Qed.

Print Assumptions typed_scalar_slot_cases.
