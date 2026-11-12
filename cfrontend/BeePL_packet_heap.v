(* Packet invariants frame actual fresh writes, independently of the scalar
   value invariant. Existing packet-containing types remain supported. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_array_object_coverage.
Require Import BeePL_initialization_proofs BeePL_structure_object_coverage BeePL_structure_storage_typing.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_state BeePL_packet_mutation BeePL_packet_coverage.
Require Import BeePL_packet_object_layout.
Import ListNotations.
Local Open Scope Z_scope.

Definition packet_layout_separated m packets (cells : scalar_layout) : Prop :=
  forall b ofs ty chunk, cells b ofs ty chunk ->
    packet_write_separated m packets b (Ptrofs.unsigned ofs)
      (size_chunk (transl_bchunk_cchunk chunk)).

Record packet_heap_invariant ge Sigma m objects cells packets : Prop := {
  packet_heap_valid : packet_state_valid m packets;
  packet_heap_typed : packet_state_typed ge.(genv_cenv) Sigma packets;
  packet_heap_coverage : packet_object_coverage ge.(genv_cenv) objects packets;
  packet_heap_separation : packet_layout_separated m packets cells;
  packet_heap_object_coherence : packet_object_coherence ge.(genv_cenv) m objects packets
}.

Lemma packet_heap_store_extension : forall ge Sigma larger m objects cells packets,
  store_context_extends Sigma larger ->
  packet_heap_invariant ge Sigma m objects cells packets ->
  packet_heap_invariant ge larger m objects cells packets.
Proof.
  intros ge Sigma larger m objects cells packets Hext [Hv Ht Hc Hs Hco].
  constructor; auto. intros b ofs Hin. eapply object_type_at_store_extension; eauto.
Qed.

Definition packet_views_preserved m final (packets : packet_locations) : Prop :=
  forall descriptor offset, packets descriptor offset -> forall view,
    packet_descriptor_valid m descriptor offset view ->
    packet_descriptor_valid final descriptor offset view.

Lemma preserved_packet_view_origin : forall m final packets,
  packet_state_valid m packets -> packet_views_preserved m final packets ->
  forall descriptor offset view, packets descriptor offset ->
    packet_descriptor_valid final descriptor offset view ->
    packet_descriptor_valid m descriptor offset view.
Proof.
  intros m final packets Hvalid Hframe descriptor offset view Hin Hview.
  destruct (Hvalid _ _ Hin) as [_ [old [bytes [Hold Hrest]]]].
  assert (view = old) by (eapply packet_descriptor_view_unique; eauto).
  subst; assumption.
Qed.

Lemma packet_write_separation_frame : forall m final packets b start count,
  packet_state_valid m packets -> packet_views_preserved m final packets ->
  packet_write_separated m packets b start count ->
  packet_write_separated final packets b start count.
Proof.
  intros m final packets b start count Hv Hframe Hsep descriptor offset Hin.
  split; [exact (proj1 (Hsep _ _ Hin))|]. intros view Hview.
  apply (proj2 (Hsep _ _ Hin) view).
  eapply preserved_packet_view_origin; eauto.
Qed.

Lemma packet_layout_separation_frame : forall m final packets cells,
  packet_state_valid m packets -> packet_views_preserved m final packets ->
  packet_layout_separated m packets cells -> packet_layout_separated final packets cells.
Proof. intros m final packets cells Hv Hf Hs b ofs ty chunk Hin.
  eapply packet_write_separation_frame; eauto. Qed.

Definition packet_block_disjoint m (packets : packet_locations) written : Prop :=
  forall descriptor offset, packets descriptor offset -> descriptor <> written /\
    forall view, packet_descriptor_valid m descriptor offset view ->
      view.(packet_block) <> written.

Lemma packet_block_disjoint_write : forall m packets written start count,
  packet_block_disjoint m packets written ->
  packet_write_separated m packets written start count.
Proof.
  intros m packets written start count H descriptor offset Hin.
  destruct (H _ _ Hin) as [Hd Hp]. split.
  - right; left; exact Hd.
  - intros view Hv. right; left; eauto.
Qed.

Lemma packet_block_disjoint_frame : forall m final packets written,
  packet_state_valid m packets -> packet_views_preserved m final packets ->
  packet_block_disjoint m packets written -> packet_block_disjoint final packets written.
Proof.
  intros m final packets written Hv Hframe Hapart descriptor offset Hin.
  split; [exact (proj1 (Hapart _ _ Hin))|]. intros view Hview.
  apply (proj2 (Hapart _ _ Hin) view). eapply preserved_packet_view_origin; eauto.
Qed.

Lemma packet_object_coherence_frames : forall cenv m final objects packets,
  packet_state_valid m packets -> packet_views_preserved m final packets ->
  packet_object_coherence cenv m objects packets -> packet_object_coherence cenv final objects packets.
Proof.
  intros cenv m final objects packets Hv Hframe Hcoherent.
  eapply packet_object_coherence_view_origins; [exact Hcoherent|].
  intros d ofs view Hin Hview. exists d, ofs. split; [exact Hin|].
  eapply preserved_packet_view_origin; eauto.
Qed.

Lemma packet_object_coherence_fresh_object : forall cenv m objects packets fresh base ty,
  packet_object_coherence cenv m objects packets -> packet_block_disjoint m packets fresh ->
  packet_object_coherence cenv m (add_aggregate_descriptor objects fresh base ty) packets.
Proof.
  intros cenv m objects packets fresh base ty Hcoherent Hapart
    b ofs root [Hold|[Hb [Hofs Hty]]] delta child Hpath descriptor offset Hin.
  - eapply Hcoherent; eauto.
  - subst. split.
    + left; right; left; exact (proj1 (Hapart _ _ Hin)).
    + intros view Hview. right; left. exact (proj2 (Hapart _ _ Hin) _ Hview).
Qed.

Lemma allocated_packet_block_disjoint : forall m packets lo hi allocated fresh,
  packet_state_valid m packets -> Mem.alloc m lo hi = (allocated, fresh) ->
  packet_block_disjoint allocated packets fresh.
Proof.
  intros m packets lo hi allocated fresh Hv Ha descriptor offset Hin.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Ha) as Hfresh.
  destruct (Hv _ _ Hin) as [_ [view [bytes [Hdesc Hrest]]]]. split.
  - intro Heq; subst. apply Hfresh. eapply packet_descriptor_source_block; eauto.
  - intros current Hcurrent Heq. apply Hfresh.
    pose proof (packet_allocation_view_origin _ _ _ _ _ _ _ _ _ Hv Ha Hin Hcurrent) as Hold.
    rewrite <- Heq. exact (proj1 (proj2 (proj2 (proj2 Hold)))).
Qed.

Theorem packet_assignment_frame : forall ge ty m written target bf value final result packets,
  packet_state_valid m packets -> packet_block_disjoint m packets written ->
  assign_addr ge ty m written target bf value final result ->
  packet_state_valid final packets /\ packet_views_preserved m final packets.
Proof.
  intros ge ty m written target bf value final result packets Hv Hap Hassign.
  inversion Hassign; subst; try discriminate;
    try match goal with Hbit : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hbit; subst end.
  all: first
    [match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in Hstore; split;
      [eapply packet_state_store_preserved; [exact Hv|apply packet_block_disjoint_write; exact Hap|exact Hstore]
      |intros descriptor offset Hin view Hview;
       eapply packet_descriptor_store_frame; [exact Hstore| |exact Hview];
       right; left; exact (proj1 (Hap _ _ Hin))] end
    |split;
      [eapply packet_state_storebytes_preserved; [exact Hv|apply packet_block_disjoint_write; exact Hap|eassumption]
      |intros descriptor offset Hin view Hview;
       eapply packet_descriptor_storebytes_disjoint; [eassumption| |exact Hview];
       left; exact (proj1 (Hap _ _ Hin))]].
Qed.

Theorem packet_array_elements_frame : forall ge m block base values ty final packets,
  packet_state_valid m packets -> packet_block_disjoint m packets block ->
  sem_array_init_helper ge m block base values ty final ->
  packet_state_valid final packets /\ packet_views_preserved m final packets /\
  packet_block_disjoint final packets block.
Proof.
  intros ge m block base values ty final packets Hv Hap Hinit.
  revert Hv Hap. induction Hinit; intros Hv Hap.
  - split; [exact Hv|]. split; [intros d o Hin current Hview; exact Hview|exact Hap].
  - destruct (packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hv Hap H) as [Hv1 Hf1].
    destruct (IHHinit Hv1 (packet_block_disjoint_frame _ _ _ _ Hv Hf1 Hap)) as [Hv2 [Hf2 Hap2]].
    split; [exact Hv2|]. split; [|exact Hap2]. intros d o Hin current Hview. eauto.
  - apply IHHinit; assumption.
Qed.

Theorem packet_field_elements_frame : forall ge block base sid fields values types m final packets,
  packet_state_valid m packets -> packet_block_disjoint m packets block ->
  sem_allocate_fields ge block base sid fields values types m final ->
  packet_state_valid final packets /\ packet_views_preserved m final packets /\
  packet_block_disjoint final packets block.
Proof.
  intros ge block base sid fields values types m final packets Hv Hap Hinit.
  revert Hv Hap. induction Hinit; intros Hv Hap.
  - split; [exact Hv|]. split; [intros d o Hin current Hview; exact Hview|exact Hap].
  - destruct (packet_assignment_frame _ _ _ _ _ _ _ _ _ _ Hv Hap H1) as [Hv1 Hf1].
    destruct (IHHinit Hv1 (packet_block_disjoint_frame _ _ _ _ Hv Hf1 Hap)) as [Hv2 [Hf2 Hap2]].
    split; [exact Hv2|]. split; [|exact Hap2]. intros d o Hin current Hview. eauto.
Qed.

Lemma primitive_array_has_no_bytes_leaf : forall env pt len attr delta,
  ~ bytes_object_leaf env (Atype (Vtype pt) len attr) delta.
Proof.
  intros env pt len attr delta Hleaf.
  destruct (primitive_array_object_paths _ _ _ _ _ _ Hleaf)
    as [[Hd Ht]|[index [Hi [Hd Ht]]]]; discriminate Ht.
Qed.

Lemma unit_array_has_no_bytes_leaf : forall env len attr delta,
  ~ bytes_object_leaf env (Atype Utype len attr) delta.
Proof.
  intros env len attr delta Hleaf.
  destruct (object_path_bounds _ _ _ _ Hleaf) as [Hd [Hs Hb]].
  change (delta + packet_descriptor_size <= 0 * Z.max 0 len) in Hb.
  pose proof packet_descriptor_size_positive; lia.
Qed.

Lemma packet_coverage_add_without_bytes : forall env objects packets block base ty,
  packet_object_coverage env objects packets ->
  (forall delta, ~ bytes_object_leaf env ty delta) ->
  packet_object_coverage env (add_aggregate_descriptor objects block base ty) packets.
Proof.
  intros env objects packets block base ty Hcoverage Hnone b ofs root [Hold|[Hb [Ho Ht]]] delta Hleaf.
  - exact (Hcoverage b ofs root Hold delta Hleaf).
  - subst. exfalso. eapply Hnone; exact Hleaf.
Qed.

Lemma packet_layout_fresh_extension : forall m packets lo hi allocated fresh cells larger,
  packet_state_valid m packets -> Mem.alloc m lo hi = (allocated, fresh) ->
  packet_layout_separated m packets cells ->
  (forall b ofs ty chunk, larger b ofs ty chunk -> cells b ofs ty chunk \/ b = fresh) ->
  packet_layout_separated allocated packets larger.
Proof.
  intros m packets lo hi allocated fresh cells larger Hv Ha Hsep Hinc b ofs ty chunk Hin.
  destruct (Hinc _ _ _ _ Hin) as [Hold|Hfresh].
  - eapply packet_allocation_preserves_write_separation; eauto.
  - subst. eapply packet_allocation_fresh_write_separated; eauto.
Qed.

Print Assumptions packet_assignment_frame.
Print Assumptions packet_array_elements_frame.
Print Assumptions packet_layout_fresh_extension.

Lemma packet_heap_fresh_array_elements :
  forall ge Sigma larger m allocated final objects cells packets lo hi fresh base values elem object_type object_base newcells,
  packet_heap_invariant ge Sigma m objects cells packets ->
  store_context_extends Sigma larger ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  sem_array_init_helper ge allocated fresh base values elem final ->
  (forall delta, ~ bytes_object_leaf ge.(genv_cenv) object_type delta) ->
  (forall b ofs ty chunk, newcells b ofs ty chunk -> cells b ofs ty chunk \/ b = fresh) ->
  packet_heap_invariant ge larger final
    (add_aggregate_descriptor objects fresh object_base object_type) newcells packets.
Proof.
  intros ge Sigma larger m allocated final objects cells packets lo hi fresh base values elem object_type object_base newcells
    [Hv Ht Hc Hs Hco] Hext Ha Hinit Hnone Hinc.
  assert (Hva : packet_state_valid allocated packets) by (eapply packet_state_allocation_preserved; eauto).
  assert (Hap : packet_block_disjoint allocated packets fresh) by (exact (allocated_packet_block_disjoint _ _ _ _ _ _ Hv Ha)).
  destruct (packet_array_elements_frame _ _ _ _ _ _ _ _ Hva Hap Hinit) as [Hvf [Hframe Hapf]].
  constructor; auto.
  - intros b ofs Hin. eapply object_type_at_store_extension; eauto.
  - eapply packet_coverage_add_without_bytes; eauto.
  - eapply packet_layout_separation_frame; [exact Hva|exact Hframe|].
    exact (packet_layout_fresh_extension m packets lo hi allocated fresh cells newcells Hv Ha Hs Hinc).
  - apply packet_object_coherence_fresh_object; [|exact Hapf].
    eapply packet_object_coherence_frames; [exact Hva|exact Hframe|].
    exact (packet_object_coherence_allocation ge.(genv_cenv) m allocated objects packets lo hi fresh Hv Hco Ha).
Qed.

Lemma packet_heap_fresh_field_elements :
  forall ge Sigma larger m allocated final objects cells packets lo hi fresh base sid fields values types object_type object_base newcells,
  packet_heap_invariant ge Sigma m objects cells packets ->
  store_context_extends Sigma larger ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  sem_allocate_fields ge fresh base sid fields values types allocated final ->
  (forall delta, ~ bytes_object_leaf ge.(genv_cenv) object_type delta) ->
  (forall b ofs ty chunk, newcells b ofs ty chunk -> cells b ofs ty chunk \/ b = fresh) ->
  packet_heap_invariant ge larger final
    (add_aggregate_descriptor objects fresh object_base object_type) newcells packets.
Proof.
  intros ge Sigma larger m allocated final objects cells packets lo hi fresh base sid fields values types object_type object_base newcells
    [Hv Ht Hc Hs Hco] Hext Ha Hinit Hnone Hinc.
  assert (Hva : packet_state_valid allocated packets) by (eapply packet_state_allocation_preserved; eauto).
  assert (Hap : packet_block_disjoint allocated packets fresh) by (exact (allocated_packet_block_disjoint _ _ _ _ _ _ Hv Ha)).
  destruct (packet_field_elements_frame _ _ _ _ _ _ _ _ _ _ Hva Hap Hinit) as [Hvf [Hframe Hapf]].
  constructor; auto.
  - intros b ofs Hin. eapply object_type_at_store_extension; eauto.
  - eapply packet_coverage_add_without_bytes; eauto.
  - eapply packet_layout_separation_frame; [exact Hva|exact Hframe|].
    exact (packet_layout_fresh_extension m packets lo hi allocated fresh cells newcells Hv Ha Hs Hinc).
  - apply packet_object_coherence_fresh_object; [|exact Hapf].
    eapply packet_object_coherence_frames; [exact Hva|exact Hframe|].
    exact (packet_object_coherence_allocation ge.(genv_cenv) m allocated objects packets lo hi fresh Hv Hco Ha).
Qed.

Lemma complete_primitive_struct_has_no_bytes_leaf : forall env sid attr co fs,
  PTree.get sid env = Some co ->
  map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members))) ->
  (forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))) ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env env) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  forall delta, ~ bytes_object_leaf env (Stype sid attr) delta.
Proof.
  intros env sid attr co fs Hco Hnames Htypes Hoffsets delta Hleaf.
  destruct (complete_primitive_struct_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hleaf)
    as [[Hd Ht]|[f [Hin [Hd Ht]]]]; discriminate Ht.
Qed.

Print Assumptions packet_heap_fresh_array_elements.
Print Assumptions packet_heap_fresh_field_elements.

Theorem packet_heap_scalar_store : forall ge Sigma m final objects cells packets b ofs ty chunk value,
  packet_heap_invariant ge Sigma m objects cells packets ->
  cells b ofs ty chunk ->
  Mem.store (transl_bchunk_cchunk chunk) m b (Ptrofs.unsigned ofs) value = Some final ->
  packet_heap_invariant ge Sigma final objects cells packets.
Proof.
  intros ge Sigma m final objects cells packets b ofs ty chunk value [Hv Ht Hc Hs Hco] Hin Hstore.
  pose proof (Hs _ _ _ _ Hin) as Hsep.
  assert (Hframe : packet_views_preserved m final packets).
  { intros descriptor offset Hentry view Hview.
    eapply packet_descriptor_store_frame; [exact Hstore|exact (proj1 (Hsep _ _ Hentry))|exact Hview]. }
  constructor; auto.
  - eapply packet_state_store_preserved; eauto.
  - eapply packet_layout_separation_frame; eauto.
  - eapply packet_object_coherence_scalar_store; eauto.
Qed.

Lemma source_primitive_struct_has_no_bytes_leaf : forall env sid attr co fs,
  PTree.get sid env = Some co ->
  map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members))) ->
  (forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))) ->
  forall delta, ~ bytes_object_leaf env (Stype sid attr) delta.
Proof.
  intros env sid attr co fs Hco Hnames Htypes.
  assert (Hpaths : forall delta ty, object_path env (Stype sid attr) delta ty ->
    ty = Stype sid attr \/ exists pt, ty = Vtype pt).
  { intros delta ty Hpath. induction Hpath.
    - left; reflexivity.
    - destruct IHHpath as [Hparent|[pt Hparent]]; [|discriminate Hparent].
      inversion Hparent; subst. assert (co0 = co) by congruence. subst co0.
      assert (Hinname : In field (map planned_field fs)).
      { rewrite Hnames. eapply full_field_name_nonpadding; eauto. }
      apply in_map_iff in Hinname. destruct Hinname as [f [Hname Hin]].
      pose proof (Htypes f Hin) as Htype. rewrite Hname in Htype.
      right. exists (planned_type f). congruence.
    - destruct IHHpath as [Hparent|[pt Hparent]]; discriminate Hparent. }
  intros delta Hleaf. destruct (Hpaths _ _ Hleaf) as [Hbad|[pt Hbad]]; discriminate Hbad.
Qed.

Theorem packet_heap_fresh_store : forall ge Sigma larger m allocated final objects cells packets lo hi fresh start chunk value newcells,
  packet_heap_invariant ge Sigma m objects cells packets ->
  store_context_extends Sigma larger ->
  Mem.alloc m lo hi = (allocated, fresh) ->
  Mem.store chunk allocated fresh start value = Some final ->
  (forall b ofs ty c, newcells b ofs ty c -> cells b ofs ty c \/ b = fresh) ->
  packet_heap_invariant ge larger final objects newcells packets.
Proof.
  intros ge Sigma larger m allocated final objects cells packets lo hi fresh start chunk value newcells
    [Hv Ht Hc Hs Hco] Hext Ha Hstore Hinc.
  assert (Hva : packet_state_valid allocated packets) by (eapply packet_state_allocation_preserved; eauto).
  assert (Hsep : packet_write_separated allocated packets fresh start (size_chunk chunk))
    by (exact (packet_allocation_fresh_write_separated m packets lo hi allocated fresh start (size_chunk chunk) Hv Ha)).
  assert (Hframe : packet_views_preserved allocated final packets).
  { intros descriptor offset Hin view Hview.
    eapply packet_descriptor_store_frame; [exact Hstore|exact (proj1 (Hsep _ _ Hin))|exact Hview]. }
  constructor; auto.
  - eapply packet_state_store_preserved; eauto.
  - intros b ofs Hin. eapply object_type_at_store_extension; eauto.
  - eapply packet_layout_separation_frame; [exact Hva|exact Hframe|].
    exact (packet_layout_fresh_extension m packets lo hi allocated fresh cells newcells Hv Ha Hs Hinc).
  - eapply packet_object_coherence_frames; [exact Hva|exact Hframe|].
    exact (packet_object_coherence_allocation ge.(genv_cenv) m allocated objects packets lo hi fresh Hv Hco Ha).
Qed.

Lemma typed_primitive_structure_no_bytes_leaf : forall env Gamma Sigma sid attr fs result ef co,
  type_expr env Gamma Sigma (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  env ! sid = Some co -> forall delta, ~ bytes_object_leaf env (Stype sid attr) delta.
Proof.
  intros env Gamma Sigma sid attr fs result ef co Htyped Hco.
  assert (Hnames : map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members)))).
  { inversion Htyped; subst. assert (co0 = co) by congruence. subst co0. assumption. }
  eapply source_primitive_struct_has_no_bytes_leaf; eauto.
  eapply typed_structure_planned_member; eauto.
Qed.

Lemma typed_planned_structure_locations : forall env Gamma Sigma sid fs result ef L,
  type_expr env Gamma Sigma (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  runtime_locations L (Sinit sid (map planned_field fs) (planned_expressions fs) result).
Proof.
  intros env Gamma Sigma sid fs result ef L Htyped. inversion Htyped; subst.
  match goal with Hargs : type_exprs _ _ _ (planned_expressions fs) _ _ |- _ =>
    destruct (typed_planned_arguments _ _ _ _ _ _ Hargs) as [Htypes Hvalues] end.
  assert (Hall : forall fields,
    (forall f, In f fields -> typeof_value (planned_value f) (Vtype (planned_type f))) ->
    all_expr_locations (runtime_locations L) (planned_expressions fields)).
  { induction fields as [|f rest IH]; intros Hvals; simpl; [exact I|]. split.
    - apply primitive_value_locations. apply Hvals; left; reflexivity.
    - apply IH. intros; apply Hvals; right; assumption. }
  simpl. apply Hall; exact Hvalues.
Qed.

Theorem packet_heap_storebytes_frame : forall ge Sigma m final objects cells packets block start bytes,
  packet_heap_invariant ge Sigma m objects cells packets ->
  packet_write_separated m packets block start (Z.of_nat (length bytes)) ->
  Mem.storebytes m block start bytes = Some final ->
  packet_heap_invariant ge Sigma final objects cells packets.
Proof.
  intros ge Sigma m final objects cells packets block start bytes [Hv Ht Hc Hs Hco] Hsep Hstore.
  assert (Hframe : packet_views_preserved m final packets).
  { intros descriptor offset Hin view Hview.
    eapply packet_descriptor_storebytes_disjoint; [exact Hstore| |exact Hview].
    pose proof (proj1 (Hsep _ _ Hin)) as Hapart.
    unfold packet_interval_disjoint in Hapart.
    pose proof packet_descriptor_size_positive. intuition lia. }
  constructor; auto.
  - eapply packet_state_storebytes_preserved; eauto.
  - eapply packet_layout_separation_frame; eauto.
  - eapply packet_object_coherence_frames; eauto.
Qed.
