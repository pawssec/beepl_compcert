(* Runtime aggregate locations entail the packet coverage needed by copying.
   Callable scalar-array layouts remain supported; their elements cannot
   contain an embedded descriptor path. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_soundness_store BeePL_soundness_memory BeePL_runtime_locations BeePL_soundness_arrays.
Require Import BeePL_callable_locations BeePL_aggregate_memory BeePL_aggregate_copy BeePL_object_paths.
Require Import BeePL_packet_descriptor_copy BeePL_object_coverage BeePL_packet BeePL_packet_state BeePL_packet_coverage.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_packet_object_layout BeePL_packet_replacement BeePL_bytes_execution.
Local Open Scope Z_scope.

Lemma by_value_array_object_paths : forall cenv elem len attr chunk delta ty,
  access_mode_type elem = By_value chunk ->
  object_path cenv (Atype elem len attr) delta ty ->
  (delta = 0 /\ ty = Atype elem len attr) \/
  exists index, 0 <= index < len /\ delta = index * sizeof_type cenv elem /\ ty = elem.
Proof.
  intros cenv elem len attr chunk delta ty Hmode Hpath.
  remember (Atype elem len attr) as root eqn:Hroot.
  induction Hpath.
  - left; auto.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent]|[i [Hi [Hbase Hparent]]]];
      [discriminate Hparent|]. subst elem. discriminate Hmode.
  - rewrite Hroot in IHHpath. destruct IHHpath as [[Hbase Hparent]|[i [Hi [Hbase Hparent]]]].
    + inversion Hparent; subst. right. exists index; repeat split; auto; lia.
    + subst elem. discriminate Hmode.
Qed.

Lemma callable_array_has_no_bytes_path : forall cenv Sigma m cells b base elem len attr delta,
  typed_memory_layout cenv Sigma cells m ->
  array_reference_locations cenv cells b base (Atype elem len attr) ->
  ~ object_path cenv (Atype elem len attr) delta Bytes.
Proof.
  intros cenv Sigma m cells b base elem len attr delta Hmemory
    [element [count [a [Heq [Hcount Hcells]]]]] Hpath.
  inversion Heq; subst element count a.
  destruct (object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hsize Hbound]].
  assert (Hlen : 0 < len).
  { destruct (Z_le_gt_dec len 0); [|lia]. simpl in Hbound.
    rewrite Z.max_l in Hbound by lia.
    change (delta + packet_descriptor_size <= sizeof_type cenv elem * 0) in Hbound.
    pose proof packet_descriptor_size_positive; unfold packet_descriptor_size in *; nia. }
  assert (Hzero : (0 < Z.to_nat len)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl; lia. }
  destruct (Hcells 0%nat Hzero) as [chunk Hcell].
  pose proof (typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)) as Hmode.
  destruct (by_value_array_object_paths _ _ _ _ _ _ _ Hmode Hpath)
    as [[Hd Ht]|[i [Hi [Hd Ht]]]]; [discriminate Ht|].
  subst elem. discriminate Hmode.
Qed.

Theorem located_aggregate_packet_coverage : forall ge Sigma m objects cells packets b base root,
  initialized_object_memory ge Sigma m objects cells ->
  packet_object_coverage ge.(genv_cenv) objects packets ->
  is_aggregate_type root = true -> packet_heap_locations ge cells objects packets b base root ->
  forall delta, object_path ge.(genv_cenv) root delta Bytes ->
    packets b (Ptrofs.repr (Ptrofs.unsigned base + delta)).
Proof.
  intros ge Sigma m objects cells packets b base root Hmemory Hcoverage Hkind Hloc delta Hpath.
  destruct Hloc as [Hloc|[Hbytes Hpacket]]; [|subst root; discriminate Hkind].
  destruct Hloc as [Hcall|[[Haggregate Hobject]|[basic [pa [Htype Hrest]]]]].
  - destruct root; simpl in Hkind; try discriminate.
    + destruct Hcall as [[pt [chunk [Hbad Hcell]]]|[elem [len [arrayAttr [Hbad Hcells]]]]]; discriminate Hbad.
    + destruct Hcall as [[pt [chunk [Hbad Hcell]]]|Harray]; [discriminate Hbad|].
      exfalso. eapply callable_array_has_no_bytes_path;
        [exact (initialized_object_cells _ _ _ _ _ Hmemory)|exact Harray|exact Hpath].
  - eapply Hcoverage; eauto.
  - subst root. discriminate Hkind.
Qed.

Lemma located_aggregate_reference_object : forall ge Sigma m objects cells packets b base basic attr,
  initialized_object_memory ge Sigma m objects cells ->
  is_aggregate_type (construct_type_btype basic) = true ->
  packet_heap_locations ge cells objects packets b base (Ptrtype (Reftype basic attr)) ->
  objects b base (construct_type_btype basic).
Proof.
  intros ge Sigma m objects cells packets b base basic attr Hmemory Hkind Hloc.
  destruct Hloc as [Hloc|[Hbad Hpacket]]; [|discriminate Hbad].
  destruct Hloc as [Hcall|[[Hbad Hobject]|[bt [pa [Ht [Hk Hobject]]]]]]; [|discriminate Hbad|inversion Ht; subst; exact Hobject].
  destruct Hcall as [[pt [chunk [Ht Hcell]]]|[elem [len [arrayAttr [Hbad Hcells]]]]]; [|discriminate Hbad].
  inversion Ht; subst pt. pose proof (typed_cell_access _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
  pose proof (by_value_type_not_aggregate _ _ Hmode) as Hnot.
  destruct basic; simpl in Hkind, Hnot; congruence.
Qed.

Theorem located_aggregate_packet_replacement_plan :
  forall ge Sigma m objects cells packets source base destination target basic attr,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_invariant ge Sigma m objects cells packets ->
  packet_heap_locations ge cells objects packets source base (construct_type_btype basic) ->
  packet_heap_locations ge cells objects packets destination target (Ptrtype (Reftype basic attr)) ->
  aggregate_copy_ready ge m (construct_type_btype basic) source base destination target ->
  packet_copy_replacement_plan m packets source (Ptrofs.unsigned base) destination
    (Ptrofs.unsigned target) (aggregate_copy_size ge (construct_type_btype basic)).
Proof.
  intros ge Sigma m objects cells packets source base destination target basic attr
    Hmemory [Hv Htypes Hcoverage Hseparation Hcoherent] Hsource Htarget Hready.
  pose proof (copy_kind _ _ _ _ _ _ _ Hready) as Hkind.
  pose proof (located_aggregate_reference_object _ _ _ _ _ _ _ _ _ _ Hmemory Hkind Htarget) as Hobject.
  pose proof (packet_object_coherence_root _ _ _ _ _ _ _ Hcoherent Hobject
    (copy_size_nonnegative _ _ _ _ _ _ _ Hready)) as Hregion.
  split.
  - intros descriptor offset Hin.
    destruct (proj1 (Hregion _ _ Hin)) as [Hapart|[delta [Hpath [Hd Ho]]]].
    + left; exact Hapart.
    + right. exists delta, (Ptrofs.repr (Ptrofs.unsigned base + delta)).
      destruct (object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hsize Hinside]].
      pose proof (copy_source_bound _ _ _ _ _ _ _ Hready) as Hextent.
      pose proof (Ptrofs.unsigned_range base) as Hbase.
      pose proof packet_descriptor_size_positive as Hpositive.
      change (delta + packet_descriptor_size <= sizeof_type ge.(genv_cenv) (construct_type_btype basic)) in Hinside.
      split; [exact Hd|]. split; [exact Ho|]. split.
      * eapply located_aggregate_packet_coverage; eauto.
      * split; [apply Ptrofs.unsigned_repr; unfold aggregate_copy_size in Hextent; unfold Ptrofs.max_unsigned; lia|].
        split; [exact Hdelta|]. split; [exact Hinside|].
        destruct (Hv _ _ Hin) as [_ [view [contents [Hdescriptor Hcontents]]]].
        rewrite <- Ho. eapply packet_descriptor_alignment; exact Hdescriptor.
  - intros descriptor offset Hin view Hview. exact (proj2 (Hregion _ _ Hin) _ Hview).
Qed.
Print Assumptions located_aggregate_packet_replacement_plan.
