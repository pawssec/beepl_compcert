Require Import BeePL_array_proofs.
(* The successful Bytes branch constructs a real fresh header object. This
   module assembles its initialized shared heap from actual packet operations. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_packet BeePL_packet_proofs BeePL_packet_state BeePL_packet_heap.
Require Import BeePL_packet_mutation BeePL_packet_descriptor_copy.
Require Import BeePL_packet_bindings BeePL_packet_coverage BeePL_packet_object_layout.
Require Import BeePL_storage_types.
Require Import BeePL_packet_schema_check BeePL_packet_header_layout BeePL_packet_header_extents.
Require Import BeePL_initialized_runtime BeePL_layout_coherence BeePL_scalar_object_layout.
Require Import BeePL_object_separation BeePL_heap_extents BeePL_block_extents.
Import ListNotations.
Local Open Scope Z_scope.

Lemma packet_preparation_old_permissions : forall env members m bytes final fresh,
  prepare_packet_header env members m bytes=OK(final,fresh) ->
  forall b ofs k perm, Mem.perm m b ofs k perm -> Mem.perm final b ofs k perm.
Proof.
  intros * Hprepare b ofs k perm Hperm.
  eapply Mem.perm_unchanged_on; [eapply prepare_packet_header_unchanged_old; exact Hprepare| |exact Hperm].
  eapply Mem.perm_valid_block; exact Hperm.
Qed.

Lemma packet_preparation_old_blocks : forall env members m bytes final fresh,
  prepare_packet_header env members m bytes=OK(final,fresh) ->
  forall b, Mem.valid_block m b -> Mem.valid_block final b.
Proof. intros. eapply Mem.valid_block_unchanged_on; [eapply prepare_packet_header_unchanged_old; eauto|assumption]. Qed.

Lemma packet_preparation_old_locations : forall env members m bytes final fresh cenv Sigma cells L,
  prepare_packet_header env members m bytes=OK(final,fresh) ->
  typed_memory_layout cenv Sigma cells m -> memory_locations L cells m ->
  memory_locations L cells final.
Proof.
  intros * Hprepare Hmemory Hlocations b ofs ty chunk Hcell v Hread.
  destruct (Hmemory _ _ _ _ Hcell) as [Hmode Hvolatile Haccess [cv [old [Hload [Hdecode Htyped]]]]].
  assert(Hold : deref_addr ty m b ofs Full old) by (eapply deref_addr_value; eauto).
  assert(Hnew : deref_addr ty final b ofs Full old).
  { eapply deref_addr_value; eauto.
    eapply Mem.load_unchanged_on; [eapply prepare_packet_header_unchanged_old; exact Hprepare| |exact Hload].
    intros. eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact Haccess|constructor]. }
  assert(v=old) by (eapply deref_full_deterministic; eauto). subst v.
  eapply Hlocations; eauto.
Qed.

Lemma packet_preparation_packet_state : forall env members m bytes final fresh packets,
  prepare_packet_header env members m bytes=OK(final,fresh) -> packet_state_valid m packets ->
  packet_state_valid final packets /\ packet_views_preserved m final packets.
Proof.
  intros * Hprepare Hv.
  assert(Hunchanged:=prepare_packet_header_unchanged_old _ _ _ _ _ _ Hprepare).
  split.
  - intros b ofs Hin. destruct (Hv _ _ Hin) as [Hbound [view [contents [Hdesc [Hload Hinit]]]]].
    destruct (initialized_packet_state_unchanged _ _ _ _ _ Hunchanged (conj Hdesc (ex_intro _ contents (conj Hload Hinit))))
      as [Hdesc' [contents' [Hload' Hinit']]].
    split; [exact Hbound|]. exists view,contents'; auto.
  - intros b ofs Hin view Hdesc.
    destruct (Hv _ _ Hin) as [_ [actual [contents [Hactual [Hload Hinit]]]]].
    assert(view=actual) by (eapply packet_descriptor_view_unique; eauto). subst view.
    exact (proj1 (initialized_packet_state_unchanged _ _ _ _ _ Hunchanged
      (conj Hactual (ex_intro _ contents (conj Hload Hinit))))).
Qed.

Lemma prepared_header_fresh : forall env members m bytes final fresh,
  prepare_packet_header env members m bytes=OK(final,fresh) -> ~Mem.valid_block m fresh.
Proof.
  intros * Hprepare.
  destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare) as [offsets [copied [_ [Hcopy _]]]].
  destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc _]].
  eapply Mem.fresh_block_alloc; exact Halloc.
Qed.

Lemma prepared_header_store_extension : forall env members Sigma m bytes final fresh sid,
  store_blocks_valid Sigma m -> prepare_packet_header env members m bytes=OK(final,fresh) ->
  store_context_extends Sigma (PTree.set fresh(Stype sid noattr) Sigma).
Proof.
  intros * Hblocks Hprepare. apply store_context_extends_fresh.
  destruct (Sigma!fresh) as [ty|] eqn:Hget; auto. exfalso.
  eapply prepared_header_fresh; [exact Hprepare|eapply Hblocks; exact Hget].
Qed.

Theorem prepared_header_objects_valid : forall p Sigma m objects cells sid co bytes final fresh,
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  PTree.get sid p.(prog_comp_env)=Some co -> co_sizeof co<=Ptrofs.max_unsigned ->
  Z.of_nat(length bytes)=co_sizeof co ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  aggregate_objects_valid p.(prog_comp_env) (PTree.set fresh(Stype sid noattr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr)).
Proof.
  intros p Sigma m objects cells sid co bytes final fresh Hmemory Hblocks Hco Hbound Hsize Hprepare.
  pose proof (prepared_header_store_extension _ _ _ _ _ _ _ sid Hblocks Hprepare) as Hext.
  pose proof (prepared_packet_header_extent _ _ _ _ _ _ Hprepare ltac:(lia)) as Hextent.
  assert(Hold : aggregate_objects_valid p.(prog_comp_env) (PTree.set fresh(Stype sid noattr) Sigma) final objects).
  { eapply aggregate_objects_valid_frame; [exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hext| |].
    - eapply packet_preparation_old_blocks; exact Hprepare.
    - eapply packet_preparation_old_permissions; exact Hprepare. }
  constructor; intros b base ty [Hobject|[Hb [Hbase Hty]]]; try solve
    [eapply aggregate_object_typing; eauto|eapply aggregate_object_readable; eauto|eapply aggregate_object_address_bound; eauto].
  - subst b base ty. rewrite Ptrofs.unsigned_zero.
    change(object_type_at p.(prog_comp_env) (PTree.set fresh(Stype sid noattr) Sigma) fresh 0
      (stored_object_type(Stype sid noattr))).
    apply object_type_root; [apply PTree.gss|]. simpl; rewrite Hco; pose proof(co_sizeof_pos co); lia.
  - subst b base ty. unfold aggregate_readable. rewrite Ptrofs.unsigned_zero.
    simpl; rewrite Hco. unfold Ptrofs.max_unsigned in Hbound. repeat split; try lia.
    + exact(source_extent_valid _ _ _ Hextent).
    + intros ofs Hrange. eapply Mem.perm_implies with (p1:=Freeable); [|constructor].
      apply(source_extent_freeable _ _ _ Hextent). rewrite Hsize; lia.
  - subst b base ty. rewrite Ptrofs.unsigned_zero; simpl; rewrite Hco; lia.
Qed.

Theorem prepared_header_initialized_memory : forall p Sigma m objects cells sid fields co bytes final fresh,
  initialized_object_memory (globalenv p) Sigma m objects cells -> store_blocks_valid Sigma m ->
  storage_safe_packet_schema p.(prog_comp_env) sid fields ->
  PTree.get sid p.(prog_comp_env)=Some co -> Z.of_nat(length bytes)=co_sizeof co ->
  initialized_packet_contents bytes ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  initialized_object_memory (globalenv p) (PTree.set fresh(Stype sid noattr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells p.(prog_comp_env) co fresh).
Proof.
  intros p Sigma m objects cells sid fields co bytes final fresh Hmemory Hblocks Hsafe Hco Hsize Hinit Hprepare.
  pose proof Hsafe as [actual [Hactual [Hstruct [Hmembers [Hfields Hstorage]]]]].
  assert(actual=co) by congruence; subst actual.
  assert(Hbound:co_sizeof co<=Ptrofs.max_unsigned).
  { pose proof(storage_type_size_bounds _ _ Hstorage) as Hb. simpl in Hb; rewrite Hco in Hb; lia. }
  pose proof(prepared_header_store_extension _ _ _ _ _ _ _ sid Hblocks Hprepare) as Hext.
  assert(Hcells:typed_memory_layout p.(prog_comp_env) (PTree.set fresh(Stype sid noattr) Sigma)
      (packet_header_layout cells p.(prog_comp_env) co fresh) final).
  { eapply safe_prepared_packet_header_cells; eauto. exact(initialized_object_cells _ _ _ _ _ Hmemory). }
  constructor.
  - eapply prepared_header_objects_valid; eauto.
  - eapply packet_header_object_coverage; [exact(initialized_object_leaves _ _ _ _ _ Hmemory)|exact Hco|exact Hmembers].
  - exact Hcells.
  - intros b ofs ty chunk Hcell v Hread. destruct Hcell as [Hold|Hnew].
    + eapply value_locations_monotone with (L:=descriptor_heap_locations (globalenv p) cells objects); [|].
      * apply descriptor_heap_locations_monotone; intros; left; assumption.
      * eapply packet_preparation_old_locations; [exact Hprepare|exact(initialized_object_cells _ _ _ _ _ Hmemory)|
          exact(initialized_object_locations _ _ _ _ _ Hmemory)|exact Hold|exact Hread].
    + destruct Hnew as [name [pt [delta [Hb [Hofs [Hty [Hchunk Hrest]]]]]]]. subst ty.
      eapply primitive_value_locations. eapply declarative_value_shape with (Gamma:=empty_context).
      eapply typed_memory_cell_read_preservation with (Gamma:=empty_context) (chunk:=chunk) (b:=b) (ofs:=ofs) (m:=final);
        [apply Hcells; right; exists name,pt,delta; auto|exact Hread].
  - destruct (prepare_packet_header_steps _ _ _ _ _ _ Hprepare) as [offsets [copied [_ [Hcopy _]]]].
    destruct (copy_packet_header_steps _ _ _ _ Hcopy) as [allocated [Halloc _]]. rewrite Hsize in Halloc.
    eapply packet_header_scalar_object_coherence; [exact(initialized_object_descriptors _ _ _ _ _ Hmemory)|
      exact(initialized_object_cells _ _ _ _ _ Hmemory)|exact(initialized_object_scalar_coherence _ _ _ _ _ Hmemory)|
      exact Hco|exact Hbound|exact Halloc].
Qed.

Lemma primitive_object_path_identity : forall env pt delta ty,
  object_path env(Vtype pt) delta ty -> delta=0 /\ ty=Vtype pt.
Proof.
  intros env pt delta ty Hpath. remember (Vtype pt) as root eqn:Hroot.
  induction Hpath; [subst; auto| |].
  - rewrite Hroot in IHHpath. destruct IHHpath as [_ Hbad]; discriminate.
  - rewrite Hroot in IHHpath. destruct IHHpath as [_ Hbad]; discriminate.
Qed.

Theorem prepared_header_layout_coherent : forall p Sigma m objects cells sid co bytes final fresh,
  typed_memory_layout p.(prog_comp_env) Sigma cells m -> coherent_layout cells ->
  scalar_object_coherence p.(prog_comp_env)
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells p.(prog_comp_env) co fresh) ->
  PTree.get sid p.(prog_comp_env)=Some co -> co_sizeof co<=Ptrofs.max_unsigned ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  coherent_layout (packet_header_layout cells p.(prog_comp_env) co fresh).
Proof.
  intros p Sigma m objects cells sid co bytes final fresh Hmemory Hcoherent Hscalar Hco Hbound Hprepare
    b ofs ty chunk Hcell other offset t ch Hother.
  pose proof(prepared_header_fresh _ _ _ _ _ _ Hprepare) as Hfresh.
  destruct Hcell as [Hold|[name [pt [delta [Hb [Hofs [Hty [Hchunk [Hmember Hfield]]]]]]]]];
    destruct Hother as [Hold'|[name' [pt' [delta' [Hb' [Hofs' [Hty' [Hchunk' [Hmember' Hfield']]]]]]]]].
  - eapply Hcoherent; eauto.
  - subst other. right; left; intro Heq; subst b. apply Hfresh.
    eapply initialized_scalar_valid_block; eapply typed_memory_cell_erasure; eapply Hmemory; exact Hold.
  - subst b. right; left; intro Heq; subst other. apply Hfresh.
    eapply initialized_scalar_valid_block; eapply typed_memory_cell_erasure; eapply Hmemory; exact Hold'.
  - subst b other ofs offset ty t chunk ch.
    pose proof(packet_header_declared_leaf _ _ _ _ _ _ Hco Hbound Hmember Hfield) as Hleaf.
    destruct (Hscalar fresh Ptrofs.zero(Stype sid noattr) (or_intror(conj eq_refl(conj eq_refl eq_refl)))
      _ _ (proj1 Hleaf) fresh(Ptrofs.repr delta')(Vtype pt')(chunk_of_ptype pt')
      ltac:(right; exists name',pt',delta'; repeat split; assumption || reflexivity)) as [[Hbad|Hapart]|[relative [[Hpath Hmode] [Hb Hposition]]]].
    + contradiction.
    + right; right. rewrite Ptrofs.unsigned_zero, Z.add_0_l in Hapart.
      rewrite !primitive_chunk_size in Hapart |- *. simpl in Hapart.
      destruct Hapart; [right|left]; rewrite ?primitive_chunk_size; assumption.
    + destruct (primitive_object_path_identity _ _ _ _ Hpath) as [Hr Htype].
      inversion Htype; subst pt'. rewrite Ptrofs.unsigned_zero in Hposition.
      (* Address equality is derived from the exact positions, not chunks. *)
      assert(Hoffset:Ptrofs.repr delta'=Ptrofs.repr delta).
      { rewrite <- (Ptrofs.repr_unsigned (Ptrofs.repr delta')), <- (Ptrofs.repr_unsigned (Ptrofs.repr delta)). f_equal; lia. }
      left. repeat split; auto.
Qed.

Theorem prepared_header_packet_heap : forall p Sigma m objects cells packets sid fields co bytes final fresh,
  packet_heap_invariant (globalenv p) Sigma m objects cells packets -> store_blocks_valid Sigma m ->
  storage_safe_packet_schema p.(prog_comp_env) sid fields ->
  PTree.get sid p.(prog_comp_env)=Some co ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  packet_heap_invariant (globalenv p) (PTree.set fresh(Stype sid noattr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells p.(prog_comp_env) co fresh) packets.
Proof.
  intros p Sigma m objects cells packets sid fields co bytes final fresh
    [Hv Htyped Hcoverage Hseparation Hcoherence] Hblocks Hsafe Hco Hprepare.
  destruct Hsafe as [actual [Hactual [Hstruct [Hmembers [Hfields Hstorage]]]]].
  assert(actual=co) by congruence; subst actual.
  destruct (packet_preparation_packet_state _ _ _ _ _ _ _ Hprepare Hv) as [Hv' Hviews].
  assert(Hapart:packet_block_disjoint final packets fresh).
  { intros d o Hin. pose proof(prepared_header_fresh _ _ _ _ _ _ Hprepare) as Hfresh.
    destruct(Hv _ _ Hin) as [_ [old [contents [Hdesc Hcontents]]]]. split.
    - intro Heq; subst d. apply Hfresh. eapply packet_descriptor_source_block; exact Hdesc.
    - intros view Hview Heq. pose proof(preserved_packet_view_origin _ _ _ Hv Hviews _ _ _ Hin Hview) as Hold.
      apply Hfresh. rewrite <-Heq. exact(proj1(proj2(proj2(proj2 Hold)))). }
  constructor.
  - exact Hv'.
  - intros b ofs Hin. eapply object_type_at_store_extension; [apply Htyped; exact Hin|].
    eapply prepared_header_store_extension; eauto.
  - eapply packet_coverage_add_without_bytes; [exact Hcoverage|].
    intros delta Hleaf. unfold bytes_object_leaf in Hleaf.
    destruct(primitive_schema_object_paths _ _ _ _ Hco Hmembers _ _ Hleaf)
      as [[_ Hbad]|[name [pt [Hbad _]]]]; discriminate.
  - intros b ofs ty chunk [Hold|[name [pt [delta [Hb Hrest]]]]].
    + eapply packet_write_separation_frame; [exact Hv|exact Hviews|]. exact(Hseparation b ofs ty chunk Hold).
    + subst b. eapply packet_block_disjoint_write; exact Hapart.
  - apply packet_object_coherence_fresh_object; [|exact Hapart].
    eapply packet_object_coherence_frames; [exact Hv|exact Hviews|exact Hcoherence].
Qed.

Theorem prepared_header_heap_evolution : forall p Gamma Sigma vm m objects cells packets sid fields co bytes final fresh,
  initialized_heap_state (globalenv p) Gamma Sigma vm m objects cells packets -> coherent_layout cells ->
  storage_safe_packet_schema p.(prog_comp_env) sid fields ->
  PTree.get sid p.(prog_comp_env)=Some co -> Z.of_nat(length bytes)=co_sizeof co ->
  initialized_packet_contents bytes ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  initialized_heap_evolution (globalenv p) Sigma objects cells packets
    (PTree.set fresh(Stype sid noattr) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells p.(prog_comp_env) co fresh) packets /\
  coherent_layout(packet_header_layout cells p.(prog_comp_env) co fresh).
Proof.
  intros p Gamma Sigma vm m objects cells packets sid fields co bytes final fresh
    [Hblocks Hmemory Hbindings Hpackets Hextents] Hcoherent Hsafe Hco Hsize Hinit Hprepare.
  pose proof Hsafe as [actual [Hactual [Hstruct [Hmembers [Hfields Hstorage]]]]].
  assert(actual=co) by congruence; subst actual.
  assert(Hbound:co_sizeof co<=Ptrofs.max_unsigned).
  { pose proof(storage_type_size_bounds _ _ Hstorage) as Hb. simpl in Hb; rewrite Hco in Hb; lia. }
  pose proof(prepared_header_initialized_memory _ _ _ _ _ _ _ _ _ _ _ Hmemory Hblocks Hsafe Hco Hsize Hinit Hprepare) as Hmemory'.
  split.
  - constructor.
    + eapply prepared_header_store_extension; eauto.
    + intros; left; assumption.
    + intros; left; assumption.
    + intros b ty Hget. eapply prepare_packet_header_valid_store; eauto.
    + exact Hmemory'.
    + auto.
    + eapply prepared_header_packet_heap; eauto.
    + eapply prepared_packet_heap_extents; [exact Hextents|exact Hprepare|lia|].
      eapply tracked_data_block_same_block_extension.
      * apply store_set_lookup_origin.
      * intros b base ty [Hold|[Hb Hrest]]; auto.
      * intros b ofs ty chunk [Hold|[name [pt [delta [Hb Hrest]]]]]; auto.
      * auto.
  - eapply prepared_header_layout_coherent; [exact(initialized_object_cells _ _ _ _ _ Hmemory)|exact Hcoherent|
      exact(initialized_object_scalar_coherence _ _ _ _ _ Hmemory')|exact Hco|exact Hbound|exact Hprepare].
Qed.

Require Import BeePL_array_proofs.
Require Import BeePL_coherent_configurations BeePL_initialized_substitution BeePL_substitution_proofs.
Require Import BeePL_callable_locations BeePL_soundness_arrays BeePL_auxlemmas BeePL_layout_proofs.

Lemma located_packet_descriptor : forall ge cells objects packets b ofs,
  packet_heap_locations ge cells objects packets b ofs Bytes -> packets b ofs.
Proof.
  intros ge cells objects packets b ofs [[Hcall|Hobject]|[_ Hp]]; [| |exact Hp].
  - destruct Hcall as [[pt [chunk [Hbad _]]]|[elem [len [attr [Hbad _]]]]]; discriminate.
  - destruct Hobject as [[Hkind _]|[basic [attr [Hbad _]]]]; discriminate.
Qed.

Lemma instantiate_packet_fields_frames : forall fields values ge Sigma cells objects packets body result,
  instantiate_field_values fields values body=OK result ->
  initialized_runtime_frames ge Sigma cells objects packets body ->
  initialized_runtime_frames ge Sigma cells objects packets result.
Proof.
  induction fields as [|[name ty] fields IH]; intros values ge Sigma cells objects packets body result Hinstantiate Hframes;
    destruct values as [|v values]; simpl in Hinstantiate; try discriminate.
  - inversion Hinstantiate; subst; exact Hframes.
  - destruct (instantiate_field_values fields values body) as [next|error] eqn:Hnext; try discriminate.
    inversion Hinstantiate; subst result. apply value_substitution_initialized_runtime_frames.
    eapply IH; eauto.
Qed.

Lemma instantiate_packet_header_frames : forall header schema fields value values ge Sigma cells objects packets body result,
  instantiate_bytes_header header schema fields value values body=OK result ->
  initialized_runtime_frames ge Sigma cells objects packets body ->
  initialized_runtime_frames ge Sigma cells objects packets result.
Proof.
  intros * Hinstantiate Hframes. unfold instantiate_bytes_header in Hinstantiate.
  destruct (instantiate_field_values fields values body) as [next|error] eqn:Hnext; try discriminate.
  inversion Hinstantiate; subst result. apply value_substitution_initialized_runtime_frames.
  eapply instantiate_packet_fields_frames; eauto.
Qed.

Theorem coherent_bytes_match_head_preservation :
  forall p Gamma Sigma vm m objects cells packets descriptor offset sid header rest fields yes no rt ef final vm' body,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Match (Val(Vloc descriptor offset) Bytes)
      [Pbytes header(Stype sid noattr)fields;Pbytes rest Bytes []] [yes;no] rt) ef rt ->
  ssem_expr (globalenv p) p vm m
    (Match (Val(Vloc descriptor offset) Bytes)
      [Pbytes header(Stype sid noattr)fields;Pbytes rest Bytes []] [yes;no] rt) final vm' body ->
  vm'=vm /\ exists Sigma' objects' cells' selected_effect,
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets body selected_effect rt /\
    sub_effect selected_effect ef=true.
Proof.
  intros p Gamma Sigma vm m objects cells packets descriptor offset sid header rest fields yes no rt ef final vm' body
    [[Hheap Htyping Hlocations Hframes] Hcoherent] Hstep.
  pose proof Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyping) as Hschemas.
  inversion Hschemas as [|? ? Hschema Hrest]; subst.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyping)
    as [_ [scrutEffect [scrutType [budget [branchEffect [Hef [Hscrut [Hpatterns [Hlength [Hbranches Hbudgets]]]]]]]]]].
  pose proof(type_rel_typeof _ _ _ _ _ _ Hscrut) as HscrutType.
  cbn [typeof_expr] in HscrutType; subst scrutType.
  pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Hscrut) as Hnil; subst scrutEffect.
  simpl in Hef; subst ef.
  pose proof (Hbranches 0%nat _ _ eq_refl eq_refl) as Hyes.
  pose proof (Hbranches 1%nat _ _ eq_refl eq_refl) as Hno.
  cbn [runtime_locations all_expr_locations initialized_runtime_frames] in Hlocations,Hframes.
  destruct Hlocations as [Hdescriptor [Hyesloc [Hnoloc HnilLoc]]].
  destruct Hframes as [_ [Hyesframes [Hnoframes HnilFrames]]].
  assert(Htracked:packets descriptor offset) by (eapply located_packet_descriptor; exact Hdescriptor).
  destruct(packet_heap_valid _ _ _ _ _ _ Hpacket _ _ Htracked)
    as [HdescriptorBound [view [payload [Hview [Hpayload Hinitialized]]]]].
  assert(Hpacketstate:initialized_packet_state m descriptor offset view).
  { split; [exact Hview|exists payload; auto]. }
  destruct(packet_match_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as [Hexecute Hvm].
  subst vm'. split; [reflexivity|].
  pose proof Hschema as [co [Hco [Hstruct [Hmembers [Hfields Hstorage]]]]].
  change(PTree.get sid (prog_comp_env p)=Some co) in Hco.
  assert(Hsafe:storage_safe_packet_schema p.(prog_comp_env) sid fields) by (exists co; auto).
  unfold execute_packet_match in Hexecute. cbn [genv_cenv globalenv] in Hexecute. rewrite Hco in Hexecute.
  destruct(read_packet_header m descriptor offset(co_sizeof co)) as [readResult|] eqn:Hread; try discriminate.
  destruct readResult as [packet bytes|packet].
  - destruct(prepare_packet_header (bcomposite_composite_env (prog_comp_env p))(co_members co) m bytes)
      as [[prepared fresh]|error] eqn:Hprepare; try discriminate.
    destruct(read_packet_fields (bcomposite_composite_env (prog_comp_env p))(bmembers_cmembers(co_members co)) prepared fresh fields)
      as [values|error] eqn:Hvalues; try discriminate.
    destruct(instantiate_bytes_header header(Stype sid noattr)fields(Vloc fresh Ptrofs.zero)values yes)
      as [result|error] eqn:Hinstantiate; try discriminate.
    cbn [genv_cenv globalenv] in Hexecute.
    rewrite ?Hprepare, ?Hvalues, ?Hinstantiate in Hexecute. inversion Hexecute; subst prepared result.
    assert(Hbytes:initialized_packet_contents bytes) by (eapply initialized_packet_state_header; eauto).
    assert(Hsize:Z.of_nat(length bytes)=co_sizeof co).
    { destruct(read_packet_header_success _ _ _ _ _ _ Hread) as [_ [_ Hload]].
      rewrite (Mem.loadbytes_length _ _ _ _ _ Hload),Z2Nat.id; [reflexivity|pose proof(co_sizeof_pos co); lia]. }
    destruct(prepared_header_heap_evolution _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hheap Hcoherent Hsafe Hco Hsize Hbytes Hprepare)
      as [Hevolution Hcoherent'].
    set(Sigma':=PTree.set fresh(Stype sid noattr)Sigma).
    set(objects':=add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr)).
    set(cells':=packet_header_layout cells(prog_comp_env p)co fresh).
    assert(Hext:store_context_extends Sigma Sigma') by (eapply prepared_header_store_extension; eauto).
    assert(Hheader:type_expr (prog_comp_env p) Gamma Sigma' (Val(Vloc fresh Ptrofs.zero)(Stype sid noattr)) [] (Stype sid noattr)).
    { apply ty_valstruct. rewrite Ptrofs.unsigned_zero.
      change(object_type_at (prog_comp_env p) Sigma' fresh 0(stored_object_type(Stype sid noattr))).
      apply object_type_root; [apply PTree.gss|]. simpl; rewrite Hco; pose proof(co_sizeof_pos co); lia. }
    destruct(prepare_packet_header_total (prog_comp_env p) sid fields co m bytes Hschema Hco (program_composites_consistent p sid co Hco) Hsize Hbytes)
      as [chosen [block [Hchosen [Hbuffer HfreshRest]]]].
    rewrite Hprepare in Hchosen; inversion Hchosen; subst chosen block.
    destruct Hbuffer as [[contents [Hcontents Hcontentsinit]] Hwrite].
    destruct(packet_schema_layout_facts _ _ _ Hschema) as [actual [Hactual [Hstruct' [Hplain Htypedfields]]]].
    change(PTree.get sid (prog_comp_env p)=Some actual) in Hactual.
    assert(actual=co) by congruence; subst actual.
    destruct(read_packet_schema_fields _ _ _ _ _ _ (prog_comp_env p) Gamma Sigma'
      (program_composites_consistent p sid co Hco) Hstruct Hplain Htypedfields Hcontents Hcontentsinit)
      as [actualValues [HactualValues Hvaluetypes]].
    rewrite Hvalues in HactualValues; inversion HactualValues; subst actualValues.
    destruct(instantiate_bytes_header_preserves_typing _ _ _ _ _ _ _ _ _ _ _ Hheader Hvaluetypes
      ltac:(eapply (proj2 typing_store_extension); [exact Hyes|exact Hext])) as [typedBody [HtypedBody Hbodytyped]].
    rewrite Hinstantiate in HtypedBody; inversion HtypedBody; subst typedBody.
    assert(Hlocinc:location_context_includes (packet_heap_locations (globalenv p)cells objects packets)
      (packet_heap_locations (globalenv p)cells' objects' packets)).
    { apply packet_heap_locations_monotone; intros; try (left; assumption); assumption. }
    exists Sigma',objects',cells', (branchEffect 0%nat). split; [exact Hevolution|]. split.
    + split; [|exact Hcoherent']. constructor.
      * eapply initialized_heap_state_evolve; [exact Hheap|exact Hevolution].
      * exact Hbodytyped.
      * eapply instantiate_bytes_header_runtime_locations; [| | |exact Hinstantiate].
        -- left; right; left; split; [reflexivity|right; auto].
        -- eapply read_packet_fields_runtime_locations; exact Hvalues.
        -- eapply runtime_locations_monotone; [exact Hlocinc|exact Hyesloc].
      * eapply instantiate_packet_header_frames; [exact Hinstantiate|].
        eapply initialized_runtime_frames_evolve; [exact Hext| | | |exact Hyesframes]; intros; try (left; assumption); assumption.
    + apply(Hbudgets 0%nat); reflexivity.
  - inversion Hexecute; subst final body.
    exists Sigma,objects,cells,(branchEffect 1%nat). split.
    + eapply initialized_heap_evolution_refl; exact Hheap.
    + split.
      * split; [|exact Hcoherent]. constructor.
        -- exact Hheap.
        -- eapply value_substitution_preserves_typing; [exact Hno|exact Hscrut].
        -- eapply value_substitution_runtime_locations; [exact Hdescriptor|exact Hnoloc].
        -- apply value_substitution_initialized_runtime_frames; exact Hnoframes.
      * apply(Hbudgets 1%nat); reflexivity.
Qed.

Theorem coherent_bytes_match_head_progress :
  forall p Gamma Sigma vm m objects cells packets descriptor offset sid header rest fields yes no rt ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Match (Val(Vloc descriptor offset) Bytes)
      [Pbytes header(Stype sid noattr)fields;Pbytes rest Bytes []] [yes;no] rt) ef rt ->
  exists final body Sigma' objects' cells' selected_effect,
    ssem_expr (globalenv p) p vm m
      (Match (Val(Vloc descriptor offset) Bytes)
        [Pbytes header(Stype sid noattr)fields;Pbytes rest Bytes []] [yes;no] rt) final vm body /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm final objects' cells' packets body selected_effect rt /\
    sub_effect selected_effect ef=true.
Proof.
  intros p Gamma Sigma vm m objects cells packets descriptor offset sid header rest fields yes no rt ef Hconfig.
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
  pose proof Hheap as [Hblocks Hmemory Hbindings Hpacket Hextents].
  assert(Htracked:packets descriptor offset).
  { eapply located_packet_descriptor; exact(proj1 Hlocations). }
  destruct(packet_heap_valid _ _ _ _ _ _ Hpacket _ _ Htracked)
    as [_ [view [payload [Hview [Hload Hinit]]]]].
  destruct(packet_match_value_progress (globalenv p) p Gamma Sigma m vm descriptor offset view sid header rest fields yes no rt ef Htyped
    (program_composites_consistent p) Hview
    ltac:(intros; eapply initialized_packet_state_header; [split; [exact Hview|exists payload; auto]|eassumption]) Hblocks)
    as [final [body [ghost [effect [Hexecute [Hstep Hrest]]]]]].
  destruct(coherent_bytes_match_head_preservation p Gamma Sigma vm m objects cells packets descriptor offset sid header rest fields yes no rt ef final vm body Hconfig Hstep)
    as [_ [Sigma' [objects' [cells' [selected_effect [Hevolution [Hfinal Hsub]]]]]]].
  exists final,body,Sigma',objects',cells',selected_effect. auto.
Qed.

Print Assumptions coherent_bytes_match_head_progress.
Print Assumptions coherent_bytes_match_head_preservation.
