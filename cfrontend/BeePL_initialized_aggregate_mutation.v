Require Import BeePL_heap_extents BeePL_block_extents.
(* The shared declared-object invariant derives the scalar copy plan for
   in-place aggregate assignment, including primitive callable-array sources. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_structure_proofs BeePL_array_proofs BeePL_copy_cells.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_scalar_location_coherence.
Require Import BeePL_packet_replacement BeePL_packet_heap BeePL_packet_location_coherence.
Require Import BeePL_initialized_runtime BeePL_layout_coherence BeePL_coherent_configurations.
Import ListNotations.
Local Open Scope Z_scope.

Theorem initialized_aggregate_assignment_memory :
  forall ge Sigma m final objects cells ty src source dst target,
  initialized_object_memory ge Sigma m objects cells ->
  aggregate_copy_ready ge m ty src source dst target ->
  scalar_copy_plan cells cells src (Ptrofs.unsigned source) dst
    (Ptrofs.unsigned target) (aggregate_copy_size ge ty) ->
  assign_addr ge ty m dst target Full (Vloc src source) final (Vloc src source) ->
  initialized_object_memory ge Sigma final objects cells.
Proof.
  intros ge Sigma m final objects cells ty src source dst target
    [Hobjects Hcoverage Hmemory Hlocations HscalarCoherence] Hready Hplan Hassign.
  destruct (aggregate_assignment_preserves_layout ge Sigma
    (descriptor_heap_locations ge cells objects) cells cells objects m final ty src source dst target
    Hready Hmemory Hlocations Hobjects Hplan Hassign) as [Hmemory' [Hlocations' Hobjects']].
  constructor; assumption.
Qed.

Theorem coherent_aggregate_assignment_preservation :
  forall ge Gamma Sigma vm m objects cells packets p basic attr src source dst target ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) ef Utype ->
  aggregate_copy_ready ge m (construct_type_btype basic) src source dst target ->
  ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) final vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil Utype /\
  sub_effect nil ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p basic attr src source dst target ef final vm' e'
    [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes] Hcoherent] Hready Hstep.
  assert (Hplan : scalar_copy_plan cells cells src (Ptrofs.unsigned source) dst
    (Ptrofs.unsigned target) (aggregate_copy_size ge (construct_type_btype basic))).
  { eapply located_aggregate_scalar_copy_plan;
      [exact Hmemory|exact (proj1 (proj2 Hlocations))|exact (proj1 Hlocations)|exact Hready]. }
  assert (Hpacketplan : packet_copy_replacement_plan m packets src (Ptrofs.unsigned source) dst
    (Ptrofs.unsigned target) (aggregate_copy_size ge (construct_type_btype basic))).
  { eapply located_aggregate_packet_replacement_plan;
      [exact Hmemory|exact Hpackets|exact (proj1 (proj2 Hlocations))|exact (proj1 Hlocations)|exact Hready]. }
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
  assert (Hmemory' : initialized_object_memory ge Sigma final objects cells).
  { eapply initialized_aggregate_assignment_memory; eauto. }
  assert (Hblocks' : store_blocks_valid Sigma final).
  { intros b ty Hget. eapply assignment_preserves_valid_blocks; [eassumption|]. eapply Hblocks; eauto. }
  assert (Hpackets' : packet_heap_invariant ge Sigma final objects cells packets).
  { match goal with Hass : assign_addr _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _
        (copy_kind _ _ _ _ _ _ _ Hready) Hass) as [bytes [Hread Hstore]] end.
    eapply packet_heap_copy_replacement; [exact (copy_size_nonnegative _ _ _ _ _ _ _ Hready)|
      exact Hpackets|exact Hpacketplan|exact Hread|exact Hstore]. }
  assert (Hextents' : heap_block_extents Sigma final objects cells packets).
  { eapply heap_extents_assignment; [exact Hextents|eassumption]. }
  split; [reflexivity|]. split; [reflexivity|]. split.
  - constructor; auto using store_context_extends_refl.
  - split; [|destruct ef; reflexivity]. split; [|exact Hcoherent]. constructor.
    + constructor; assumption.
    + constructor.
    + exact I.
    + exact I.
Qed.

Theorem coherent_aggregate_assignment_progress :
  forall ge Gamma Sigma vm m objects cells packets p basic attr src source dst target ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) ef Utype ->
  aggregate_copy_ready ge m (construct_type_btype basic) src source dst target ->
  exists final,
    ssem_expr ge p vm m
      (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
        Val (Vloc src source) (construct_type_btype basic)] Utype) final vm (Val Vunit Utype) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm final objects cells packets (Val Vunit Utype) nil Utype.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p basic attr src source dst target ef Hconfig Hready.
  destruct (aggregate_massgn_progress ge p vm m basic attr src source dst target Hready) as [final Hstep].
  destruct (coherent_aggregate_assignment_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfig Hready Hstep) as [_ [_ [Hevolution [Hfinal Hsub]]]].
  exists final. auto.
Qed.

(* An exact destination footprint excludes foreign cells in copied bytes.
   It is a property of the PRE-state layout, not of the copied contents. *)
Definition primitive_array_target_footprint (cells : scalar_layout) dst pt count : Prop :=
  forall ofs ty chunk, cells dst ofs ty chunk ->
    0 < Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) ->
    Ptrofs.unsigned ofs < sizeof_ptype pt * Z.of_nat count ->
    exists i, (i < count)%nat /\ ofs = Ptrofs.repr (Z.of_nat i * sizeof_ptype pt) /\
      ty = Vtype pt /\ chunk = chunk_of_ptype pt.

Theorem primitive_array_existing_copy_plan : forall cells src dst pt count,
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  (forall i, (i < count)%nat -> cells src (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt))
    (Vtype pt) (chunk_of_ptype pt)) ->
  primitive_array_target_footprint cells dst pt count ->
  scalar_copy_plan cells cells src 0 dst 0 (sizeof_ptype pt * Z.of_nat count).
Proof.
  intros cells src dst pt count Hbound Hsource Hfoot b ofs ty chunk Hcell.
  destruct (peq b dst) as [Hb|Hb]; [subst b|left; split; [exact Hcell|left; exact Hb]].
  destruct (Z_le_gt_dec (Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk)) 0) as [Hbefore|Hbefore].
  { left. split; [exact Hcell|right; left; exact Hbefore]. }
  destruct (Z_le_gt_dec (sizeof_ptype pt * Z.of_nat count) (Ptrofs.unsigned ofs)) as [Hafter|Hafter].
  { left. split; [exact Hcell|right; right; exact Hafter]. }
  destruct (Hfoot _ _ _ Hcell ltac:(lia) ltac:(lia)) as [i [Hi [Hofs [Hty Hchunk]]]].
  subst ofs ty chunk. right. split; [reflexivity|].
  exists (Z.of_nat i * sizeof_ptype pt), (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt)).
  pose proof (primitive_size_positive pt) as Hsize.
  pose proof Hi as Hindex. apply Nat2Z.inj_lt in Hindex.
  assert (Hrange : 0 <= Z.of_nat i * sizeof_ptype pt <= Ptrofs.max_unsigned) by nia.
  split; [apply Hsource; exact Hi|]. split; [nia|]. split.
  - rewrite primitive_chunk_size. nia.
  - rewrite Ptrofs.unsigned_repr by exact Hrange. split; [lia|]. split; [lia|].
    rewrite primitive_chunk_alignment. exists (Z.of_nat i). reflexivity.
Qed.

Print Assumptions initialized_aggregate_assignment_memory.
Print Assumptions coherent_aggregate_assignment_preservation.
Print Assumptions coherent_aggregate_assignment_progress.
Print Assumptions primitive_array_existing_copy_plan.

Theorem coherent_primitive_array_target_footprint : forall cells dst pt count,
  coherent_layout cells ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  (forall i, (i < count)%nat -> cells dst (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt))
    (Vtype pt) (chunk_of_ptype pt)) ->
  primitive_array_target_footprint cells dst pt count.
Proof.
  intros cells dst pt count Hcoherent Hbound Htiling ofs ty chunk Hcell Hend Hstart.
  pose proof (primitive_size_positive pt) as Hsize.
  pose proof (Ptrofs.unsigned_range ofs) as Hrange.
  set (q := Ptrofs.unsigned ofs / sizeof_ptype pt).
  assert (Hqnonnegative : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (Hqlt : q < Z.of_nat count).
  { unfold q. apply Z.div_lt_upper_bound; nia. }
  assert (Hdecomp : Ptrofs.unsigned ofs = sizeof_ptype pt * q + Ptrofs.unsigned ofs mod sizeof_ptype pt).
  { unfold q. apply Z.div_mod. lia. }
  pose proof (Z.mod_pos_bound (Ptrofs.unsigned ofs) (sizeof_ptype pt) Hsize) as Hmod.
  set (i := Z.to_nat q).
  assert (Hiq : Z.of_nat i = q) by (unfold i; apply Z2Nat.id; exact Hqnonnegative).
  assert (Hi : (i < count)%nat) by (apply Nat2Z.inj_lt; rewrite Hiq; exact Hqlt).
  pose proof (Htiling i Hi) as Hcanonical.
  pose proof (Hcoherent _ _ _ _ Hcanonical _ _ _ _ Hcell) as Hcompatible.
  assert (Hoffset : 0 <= Z.of_nat i * sizeof_ptype pt <= Ptrofs.max_unsigned) by (rewrite Hiq; nia).
  rewrite Ptrofs.unsigned_repr in Hcompatible by exact Hoffset.
  rewrite primitive_chunk_size in Hcompatible.
  destruct Hcompatible as [[Hb [Hofs [Hty Hchunk]]]|[Hneq|[Hafter|Hbefore]]].
  - exists i. repeat split; assumption.
  - contradiction.
  - rewrite Hiq in Hafter. nia.
  - rewrite Hiq in Hbefore. pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)). nia.
Qed.

Corollary coherent_primitive_array_existing_copy_plan : forall cells src dst pt count,
  coherent_layout cells -> sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  (forall b, b = src \/ b = dst -> forall i, (i < count)%nat ->
    cells b (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt)) (Vtype pt) (chunk_of_ptype pt)) ->
  scalar_copy_plan cells cells src 0 dst 0 (sizeof_ptype pt * Z.of_nat count).
Proof.
  intros cells src dst pt count Hcoherent Hbound Htiling.
  apply primitive_array_existing_copy_plan; [exact Hbound| |].
  - intros i Hi. apply Htiling; auto.
  - apply coherent_primitive_array_target_footprint; try assumption.
    intros i Hi. apply Htiling; auto.
Qed.

Print Assumptions coherent_primitive_array_target_footprint.
Print Assumptions coherent_primitive_array_existing_copy_plan.

Lemma primitive_array_coverage_canonical_cells : forall cenv objects cells b pt count attr,
  initialized_object_coverage cenv objects cells ->
  objects b Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr) ->
  forall i, (i < count)%nat -> cells b (Ptrofs.repr (Z.of_nat i * sizeof_ptype pt))
    (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros cenv objects cells b pt count attr Hcoverage Hobject i Hi.
  assert (Hleaf : scalar_object_leaf cenv (Atype (Vtype pt) (Z.of_nat count) attr)
    (Z.of_nat i * sizeof_ptype pt) (Vtype pt) (chunk_of_ptype pt)).
  { split; [|apply primitive_chunk_access].
    change (object_path cenv (Atype (Vtype pt) (Z.of_nat count) attr)
      (0 + Z.of_nat i * sizeof_type cenv (Vtype pt)) (Vtype pt)).
    eapply path_array_element.
    - constructor. apply primitive_array_size_nonnegative.
    - split; [lia|]. apply Nat2Z.inj_lt; exact Hi.
    - simpl. pose proof (primitive_size_positive pt); lia. }
  destruct (Hcoverage _ _ _ Hobject _ _ _ Hleaf) as [stored [Hcell Hchunk]].
  assert (stored = chunk_of_ptype pt).
  { revert Hchunk. generalize (chunk_of_ptype pt). intros other Hchunk.
    destruct stored, other; simpl in Hchunk; congruence. }
  subst stored. rewrite Ptrofs.unsigned_zero, Z.add_0_l in Hcell. exact Hcell.
Qed.

Theorem covered_coherent_primitive_array_copy_plan : forall cenv objects cells src dst pt count attr,
  coherent_layout cells -> initialized_object_coverage cenv objects cells ->
  objects src Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr) ->
  objects dst Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  scalar_copy_plan cells cells src 0 dst 0 (sizeof_ptype pt * Z.of_nat count).
Proof.
  intros cenv objects cells src dst pt count attr Hcoherent Hcoverage Hsrc Hdst Hbound.
  apply coherent_primitive_array_existing_copy_plan; try assumption.
  intros b [Hb|Hb] i Hi; subst b; eapply primitive_array_coverage_canonical_cells; eauto.
Qed.

Print Assumptions covered_coherent_primitive_array_copy_plan.
