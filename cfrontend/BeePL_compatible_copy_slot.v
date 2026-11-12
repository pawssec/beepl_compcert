(* A copy slot may replace already-initialized declared aliases. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_copy_cells BeePL_initializer_slot BeePL_structure_copy_slots BeePL_layout_coherence.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_coverage BeePL_packet_replacement.
Require Import BeePL_object_paths BeePL_bytes_execution.
Local Open Scope Z_scope.

Theorem replacement_slot_packet_state : forall cenv root packets m final src source dst target bytes,
  0 <= sizeof_type cenv root -> 0 <= source -> source+sizeof_type cenv root <= Ptrofs.modulus ->
  0 <= target -> target+sizeof_type cenv root <= Ptrofs.modulus ->
  packet_state_valid m packets ->
  (forall delta, object_path cenv root delta Bytes -> packets src (Ptrofs.repr(source+delta))) ->
  (forall delta, object_path cenv root delta Bytes -> (align_chunk Mptr | target+delta)) ->
  packet_copy_replacement_plan m packets src source dst target (sizeof_type cenv root) ->
  Mem.loadbytes m src source (sizeof_type cenv root) = Some bytes ->
  Mem.storebytes m dst target bytes = Some final ->
  packet_state_valid final (slot_copy_packets cenv packets root dst target).
Proof.
  intros cenv root packets m final src source dst target bytes Hsize Hsource HsourceEnd Htarget HtargetEnd
    Hpackets Hcoverage Halign Hreplacement Hread Hstore.
  assert (Hlength : Z.of_nat(length bytes)=sizeof_type cenv root)
    by (rewrite (Mem.loadbytes_length _ _ _ _ _ Hread),Z2Nat.id; auto).
  assert (Hold : packet_state_valid final packets).
  { exact(proj1(packet_copy_replacement_state _ _ _ _ _ _ _ _ _ Hsize Hpackets Hreplacement Hread Hstore)). }
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
    pose proof (proj2 Hreplacement _ _ Hentry view Hdescriptor) as Haway.
    unfold packet_interval_disjoint in Haway.
    destruct Haway as [Hzero|Haway].
    + rewrite Hzero in *. rewrite Mem.loadbytes_empty in * by lia; exact Hcontents.
    + pose proof (proj1 (proj2 (proj2 Hdescriptor))) as Horder.
      rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ Hstore); [exact Hcontents|lia|]. rewrite Hlength; exact Haway.
Qed.

Theorem scalar_copy_plan_coherent : forall before after src source dst target count,
 coherent_layout before -> scalar_copy_plan before after src source dst target count ->
 coherent_layout after.
Proof.
 intros * Hcoherent Hplan b ofs ty chunk Hcell old off t ch Hold.
 destruct(Hplan _ _ _ _ Hcell) as [[Hbefore Haway]|[Hb [delta [origin [Hsource [Hd [Hinside [Ho [Ht Ha]]]]]]]]];
 destruct(Hplan _ _ _ _ Hold) as [[Hbefore' Haway']|[Hb' [delta' [origin' [Hsource' [Hd' [Hinside' [Ho' [Ht' Ha']]]]]]]]].
 - eapply Hcoherent;eauto.
 - subst old;right;destruct Haway as [Hneq|[Hleft|Hright]];[left;congruence|right;left;lia|right;right;lia].
 - subst b;right;destruct Haway' as [Hneq|[Hleft|Hright]];[left;exact Hneq|right;right;lia|right;left;lia].
 - subst b old. destruct(Hcoherent _ _ _ _ Hsource _ _ _ _ Hsource')
   as [[Hb [Hofs [Hty Hchunk]]]|[Hneq|[Hleft|Hright]]].
   + subst origin' t ch. assert(ofs=off) by(rewrite <- (Ptrofs.repr_unsigned ofs), <- (Ptrofs.repr_unsigned off);f_equal;lia). subst off;left;auto.
   + contradiction.
   + right;right;left;lia.
   + right;right;right;lia.
Qed.

Require Import BeePL_scalar_object_layout BeePL_packet_object_layout.
Theorem initialize_compatible_copy_slot : forall ge Sigma L cells packets m root src source dst target,
  initializer_copy_ready ge m root src source dst target ->
  typed_memory_layout ge.(genv_cenv) Sigma cells m -> memory_locations L cells m ->
  scalar_object_region_coherent ge.(genv_cenv) cells dst (Ptrofs.unsigned target) root ->
  (forall delta ty chunk, scalar_object_leaf ge.(genv_cenv) root delta ty chunk ->
    exists stored, cells src(Ptrofs.repr(Ptrofs.unsigned source+delta)) ty stored /\
    transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) ->
  slot_copy_alignment cells src (Ptrofs.unsigned source) (Ptrofs.unsigned target) (sizeof_type ge.(genv_cenv) root) ->
  packet_state_valid m packets ->
  (forall delta, object_path ge.(genv_cenv) root delta Bytes ->
    packets src (Ptrofs.repr(Ptrofs.unsigned source+delta))) ->
  (forall delta, object_path ge.(genv_cenv) root delta Bytes ->
    (align_chunk Mptr | Ptrofs.unsigned target+delta)) ->
  packet_object_region_coherent ge.(genv_cenv) m packets dst (Ptrofs.unsigned target) root ->
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
    Hcells Hlocations Hregion HscalarCoverage Halign Hpackets Hcoverage HpacketAlign HpacketRegion.
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
    ltac:(eapply declared_field_copy_layout_plan; eauto; pose proof(Ptrofs.unsigned_range source); pose proof(Ptrofs.unsigned_range target); lia)) as [Hcells' Hlocations'].
  exists final,bytes. split; [exact Hbytes|]. split; [exact Hstore|]. split; [exact Hassign|].
  split; [exact Hcells'|]. split; [exact Hlocations'|].
  assert (Hreplacement:packet_copy_replacement_plan m packets src(Ptrofs.unsigned source) dst(Ptrofs.unsigned target)(sizeof_type ge.(genv_cenv) root)).
  { eapply declared_field_packet_replacement_plan; eauto;pose proof(Ptrofs.unsigned_range source);lia. }
  eapply (replacement_slot_packet_state ge.(genv_cenv) root packets m final src (Ptrofs.unsigned source) dst (Ptrofs.unsigned target) bytes); eauto; pose proof(Ptrofs.unsigned_range source); pose proof(Ptrofs.unsigned_range target); lia.
Qed.


Print Assumptions initialize_compatible_copy_slot.
