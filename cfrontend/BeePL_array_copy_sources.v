(* Source facts for copying initializers are derived from the shared heap. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory.
Require Import BeePL_scalar_object_layout BeePL_object_separation.
Require Import BeePL_packet BeePL_packet_state BeePL_packet_descriptor_copy BeePL_packet_heap BeePL_packet_coverage.
Require Import BeePL_bytes_execution BeePL_general_array_initialization.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bytes_object_path_identity : forall env delta ty,
  object_path env Bytes delta ty -> delta=0 /\ ty=Bytes.
Proof.
  intros env delta ty Hpath;remember Bytes as root eqn:Hroot;induction Hpath.
  - auto.
  - destruct IHHpath as [_ Hbad];rewrite Hroot in Hbad;discriminate.
  - destruct IHHpath as [_ Hbad];rewrite Hroot in Hbad;discriminate.
Qed.

Theorem tracked_aggregate_array_copy_source : forall ge p Sigma m objects cells packets dst src base root,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_invariant ge Sigma m objects cells packets ->
  objects src base root -> ~Mem.valid_block m dst ->
  array_copy_source ge.(genv_cenv) cells packets m dst root(Vloc src base).
Proof.
  intros ge p Sigma m objects cells packets dst src base root Henv Hmemory Hpackets Hobject Hfresh.
  pose proof(initialized_object_descriptors _ _ _ _ _ Hmemory) as Hobjects.
  destruct(aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [Hkind [Hsize [Hbound [Hvalid Hread]]]].
  assert(HcopyAlign:(alignof_blockcopy(bcomposite_composite_env ge.(genv_cenv))(transBeePL_type root)|Ptrofs.unsigned base)).
  { rewrite Henv. apply(program_typed_object_copy_alignment p Sigma src(Ptrofs.unsigned base) root).
    rewrite <-Henv;eapply aggregate_object_typing;eauto. }
  eapply array_copy_source_intro with(src:=src)(source:=base);try assumption;try reflexivity.
  - intro Heq;subst;contradiction.
  - destruct root;simpl in Hkind;try discriminate;exact HcopyAlign.
  - intros delta ty chunk Hleaf;eapply initialized_object_leaves;eauto.
  - intros Hpositive delta child Hpath;eapply initialized_object_scalar_coherence;eauto.
  - intros delta Hpath;eapply packet_heap_coverage;eauto.
Qed.

Theorem tracked_bytes_array_copy_source : forall ge Sigma m objects cells packets dst src base,
  packet_heap_invariant ge Sigma m objects cells packets ->
  packets src base -> ~Mem.valid_block m dst ->
  array_copy_source ge.(genv_cenv) cells packets m dst Bytes(Vloc src base).
Proof.
  intros ge Sigma m objects cells packets dst src base Hpackets Hsource Hfresh.
  destruct(packet_heap_valid _ _ _ _ _ _ Hpackets _ _ Hsource)
    as [Hbound [view [contents [Hdescriptor [Hcontents Hinitialized]]]]].
  pose proof(packet_descriptor_source_block _ _ _ _ Hdescriptor) as Hvalid.
  destruct(packet_descriptor_loadbytes _ _ _ _ Hdescriptor) as [bytes Hread].
  eapply array_copy_source_intro with(src:=src)(source:=base);try reflexivity;try assumption.
  - intro Heq;subst;contradiction.
  - eapply packet_descriptor_alignment;exact Hdescriptor.
  - eapply Mem.loadbytes_range_perm;exact Hread.
  - intros delta ty chunk [Hpath Hmode].
    destruct(bytes_object_path_identity _ _ _ Hpath) as [Hd Hty];subst;simpl in Hmode;discriminate.
  - intros Hpositive delta child Hpath.
    destruct(bytes_object_path_identity _ _ _ Hpath) as [Hd Hty];subst.
    rewrite Z.add_0_r. intros b ofs ty chunk Hcell. left.
    destruct(packet_heap_separation _ _ _ _ _ _ Hpackets _ _ _ _ Hcell _ _ Hsource) as [Hapart Hpayload].
    unfold packet_interval_disjoint in Hapart.
    pose proof packet_descriptor_size_positive. change(sizeof_type ge.(genv_cenv) Bytes) with packet_descriptor_size.
    intuition (try congruence;lia).
  - intros delta Hpath. destruct(bytes_object_path_identity _ _ _ Hpath) as [Hd Hty];subst delta.
    rewrite Z.add_0_r,Ptrofs.repr_unsigned;exact Hsource.
Qed.

Lemma array_copy_sources_allocation_frame : forall env seed packets m allocated low high dst root values fresh,
  Forall(array_copy_source env seed packets m dst root) values ->
  Mem.alloc m low high=(allocated,fresh) ->
  Forall(array_copy_source env seed packets allocated dst root) values.
Proof.
  intros env seed packets m allocated low high dst root values fresh Hsources Halloc.
  eapply Forall_impl;[|exact Hsources]. intros v Hsource.
  destruct Hsource as [src source Hv Hapart Hvalid Hbound Halign Hread Hleaves Hregions Hpackets].
  eapply array_copy_source_intro with(src:=src)(source:=source);try assumption.
  - eapply Mem.valid_block_alloc;eauto.
  - intros position Hin;eapply Mem.perm_alloc_1;[exact Halloc|apply Hread;exact Hin].
Qed.

Require Import BeePL_callable_scalar_arrays BeePL_layout_coherence BeePL_heap_extents.
Require Import BeePL_soundness_arrays BeePL_callable_locations BeePL_packet_bindings BeePL_packet_location_coherence.

Theorem callable_array_copy_source : forall ge p Sigma m objects cells packets dst src base elem len attr,
  ge.(genv_cenv)=p.(prog_comp_env) -> initialized_object_memory ge Sigma m objects cells ->
  coherent_layout cells -> heap_block_extents Sigma m objects cells packets ->
  object_type_at ge.(genv_cenv) Sigma src(Ptrofs.unsigned base)(Atype elem len attr) ->
  array_reference_locations ge.(genv_cenv) cells src base(Atype elem len attr) ->
  ~Mem.valid_block m dst ->
  array_copy_source ge.(genv_cenv) cells packets m dst(Atype elem len attr)(Vloc src base).
Proof.
  intros ge p Sigma m objects cells packets dst src base elem len attr Henv Hmemory Hcoherent Hextents Hobject Harray Hfresh.
  destruct(callable_scalar_array_readable _ _ _ _ _ _ _ _ _ _ _ Hmemory Hextents Hobject Harray)
    as [[Hkind [Hsize [Hbound [Hvalid Hread]]]] Haddress].
  eapply array_copy_source_intro with(src:=src)(source:=base);try assumption;try reflexivity.
  - intro Heq;subst;contradiction.
  - change (alignof_blockcopy(bcomposite_composite_env ge.(genv_cenv))(transBeePL_type(Atype elem len attr))|Ptrofs.unsigned base).
    rewrite Henv. apply(program_typed_object_copy_alignment p Sigma src(Ptrofs.unsigned base)(Atype elem len attr)).
    rewrite <-Henv;exact Hobject.
  - eapply callable_scalar_array_coverage;[exact(initialized_object_cells _ _ _ _ _ Hmemory)|exact Harray|exact Haddress].
  - intros Hpositive delta child Hpath.
    pose proof(initialized_object_cells _ _ _ _ _ Hmemory) as Hcells.
    rewrite Henv in Hcells,Harray,Haddress,Hpositive,Hpath |- *.
    eapply callable_scalar_array_regions;eauto.
  - intros delta Hpath;exfalso;eapply callable_array_has_no_bytes_path;
      [exact(initialized_object_cells _ _ _ _ _ Hmemory)|exact Harray|exact Hpath].
Qed.

Lemma typed_copy_value_canonical : forall env Gamma Sigma v root,
  type_expr env Gamma Sigma(Val v root) nil root ->
  is_aggregate_type root=true \/ root=Bytes ->
  exists b base,v=Vloc b base /\ object_type_at env Sigma b(Ptrofs.unsigned base) root.
Proof.
  intros env Gamma Sigma v root Htyped Hkind;destruct root;simpl in Hkind;
    try solve[destruct Hkind;discriminate];inversion Htyped;subst;eauto.
Qed.

Theorem typed_located_array_copy_source : forall ge p Gamma Sigma m objects cells packets dst root v,
  ge.(genv_cenv)=p.(prog_comp_env) -> initialized_object_memory ge Sigma m objects cells ->
  coherent_layout cells -> packet_heap_invariant ge Sigma m objects cells packets ->
  heap_block_extents Sigma m objects cells packets ->
  type_expr ge.(genv_cenv) Gamma Sigma(Val v root) nil root ->
  value_locations(packet_heap_locations ge cells objects packets) v root ->
  is_aggregate_type root=true \/ root=Bytes -> ~Mem.valid_block m dst ->
  array_copy_source ge.(genv_cenv) cells packets m dst root v.
Proof.
  intros ge p Gamma Sigma m objects cells packets dst root v Henv Hmemory Hcoherent Hpackets Hextents Htyped Hloc Hkind Hfresh.
  destruct(typed_copy_value_canonical _ _ _ _ _ Htyped Hkind) as [src [base [Hv Hobject]]];subst v.
  change(packet_heap_locations ge cells objects packets src base root) in Hloc.
  destruct Hloc as [[Hcall|[[Haggregate Htracked]|[basic [pa [Hty Hrest]]]]]|[Hbytes Hregistered]].
  - destruct root;simpl in Hkind;try solve[destruct Hkind;discriminate];
      destruct Hcall as [[pt [chunk [Hbad Hcell]]]|Harray];try discriminate Hbad.
    + destruct Harray as [e [n [arrayAttr2 [Hbad Hother]]]];discriminate Hbad.
    + eapply callable_array_copy_source;eauto.
    + destruct Harray as [e [n [arrayAttr2 [Hbad Hother]]]];discriminate Hbad.
  - eapply tracked_aggregate_array_copy_source;eauto.
  - subst root;destruct Hkind;discriminate.
  - subst root;eapply tracked_bytes_array_copy_source;eauto.
Qed.
