(* Recover hereditary declared-object coherence from exact copy provenance. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors Coqlib.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_object_paths BeePL_scalar_object_layout BeePL_general_array_initialization.
Require Import BeePL_copy_array_initialization.
Require Import BeePL_packet_state BeePL_packet_descriptor_copy.
Import ListNotations.
Local Open Scope Z_scope.

Theorem copy_array_declared_regions : forall env seed packets m values root dst start before after attr,
  0<=start -> 0<=sizeof_type env root ->
  start+Z.of_nat(length values)*sizeof_type env root<=Ptrofs.modulus ->
  Forall(array_copy_source env seed packets m dst root) values ->
  array_cells_prefix before dst start ->
  (forall b ofs ty chunk,after b ofs ty chunk -> before b ofs ty chunk \/
    copied_array_cell env seed values root dst start b ofs ty chunk) ->
  forall delta child,object_path env(Atype root(Z.of_nat(length values)) attr) delta child ->
    scalar_object_region_coherent env after dst(start+delta) child.
Proof.
  intros env seed packets m values root dst start before after attr Hstart Hsize Hend Hsources Hprefix Hprovenance
    delta child Hpath b ofs ty chunk Hcell.
  pose proof(object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hchild Hinside]].
  destruct(Hprovenance _ _ _ _ Hcell) as [Hold|Hcopied].
  - left. destruct(Hprefix _ _ _ _ Hold);[left;assumption|right;left;lia].
  - destruct Hcopied as [index [src [source [old [shift [Hnth [Hseed [HsourceOffset [Hshift [HcellEnd [Hb Hofs]]]]]]]]]]].
    subst b ofs. assert(Hindex:(index<length values)%nat).
    { apply nth_error_Some;rewrite Hnth;discriminate. }
    assert(Hsource:array_copy_source env seed packets m dst root(Vloc src source)).
    { rewrite Forall_forall in Hsources;apply Hsources. eapply nth_error_In;exact Hnth. }
    destruct Hsource as [sourceBlock sourceOffset Hvalue Hapart Hvalid Hbound Halign Hread Hleaves Hregions Hbytes].
    inversion Hvalue;subst sourceBlock sourceOffset.
    pose proof(size_chunk_pos(transl_bchunk_cchunk chunk)) as Hpositive.
    assert(Hrepr:Ptrofs.unsigned(Ptrofs.repr(start+Z.of_nat index*sizeof_type env root+shift))=
      start+Z.of_nat index*sizeof_type env root+shift).
    { apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;nia. }
    destruct(array_object_path_decomposition _ _ _ _ _ _ Hpath) as [[Hzero Hroot]|[which [relative [Hwhich [HdeltaEq Hsubpath]]]]].
    + subst delta child. destruct(Hregions ltac:(lia) 0 root ltac:(constructor;exact Hsize) _ _ _ _ Hseed)
        as [[Hneq|[Hbefore|Hafter]]|[leaf [Hleaf [Heq HleafOffset]]]].
      * contradiction.
      * lia.
      * lia.
      * right. exists(Z.of_nat index*sizeof_type env root+leaf). split.
        -- destruct Hleaf as [Hleaf Hmode]. split;[|exact Hmode].
           eapply object_path_compose;[|exact Hleaf].
           replace(Z.of_nat index*sizeof_type env root) with(0+Z.of_nat index*sizeof_type env root) by lia.
           eapply path_array_element;[constructor;simpl;nia|lia|exact Hsize].
        -- split;[reflexivity|]. rewrite Hrepr;lia.
    + pose proof(object_path_bounds _ _ _ _ Hsubpath) as [Hrelative [HchildSize HchildInside]].
      destruct(Z.lt_trichotomy (Z.of_nat index) which) as [Hlt|[Hequal|Hgt]].
      * left;right;left;rewrite Hrepr;nia.
      * destruct(Hregions ltac:(lia) relative child Hsubpath _ _ _ _ Hseed)
          as [[Hneq|[Hbefore|Hafter]]|[leaf [Hleaf [Heq HleafOffset]]]].
        -- contradiction.
        -- left;right;left;rewrite Hrepr;nia.
        -- left;right;right;rewrite Hrepr;nia.
        -- right;exists leaf;split;[exact Hleaf|]. split;[reflexivity|]. rewrite Hrepr;nia.
      * left;right;right;rewrite Hrepr;nia.
Qed.

Print Assumptions copy_array_declared_regions.

Definition copied_array_packets env (before:packet_locations) (values:list value) root dst start : packet_locations :=
  fun b ofs=>before b ofs \/ exists index delta,
    (index<length values)%nat /\ object_path env root delta Bytes /\
    b=dst /\ ofs=Ptrofs.repr(start+Z.of_nat index*sizeof_type env root+delta).

Lemma copied_array_packets_valid : forall env before after values root dst start m,
  packet_state_valid m after ->
  (forall b ofs,before b ofs -> after b ofs) ->
  (forall index delta,(index<length values)%nat -> object_path env root delta Bytes ->
    after dst(Ptrofs.repr(start+Z.of_nat index*sizeof_type env root+delta))) ->
  packet_state_valid m(copied_array_packets env before values root dst start).
Proof.
  intros env before after values root dst start m Hvalid Hbefore Hcoverage.
  eapply packet_state_valid_subcontext;[exact Hvalid|].
  intros b ofs [Hold|[index [delta [Hi [Hpath [Hb Hofs]]]]]].
  - apply Hbefore;exact Hold.
  - subst;eapply Hcoverage;eauto.
Qed.

Lemma array_path_from_index : forall env root count attr index delta ty,
  (index<count)%nat -> 0<=sizeof_type env root -> object_path env root delta ty ->
  object_path env(Atype root(Z.of_nat count) attr)(Z.of_nat index*sizeof_type env root+delta) ty.
Proof.
  intros env root count attr index delta ty Hi Hsize Hpath.
  eapply object_path_compose;[|exact Hpath].
  replace(Z.of_nat index*sizeof_type env root) with(0+Z.of_nat index*sizeof_type env root) by lia.
  eapply path_array_element;[constructor;simpl;nia|lia|exact Hsize].
Qed.

Lemma copied_array_packets_typed : forall env Sigma before values root dst start attr,
  packet_state_typed env Sigma before ->
  object_type_at env Sigma dst start(Atype root(Z.of_nat(length values)) attr) ->
  0<=start -> 0<=sizeof_type env root ->
  start+Z.of_nat(length values)*sizeof_type env root<=Ptrofs.modulus ->
  packet_state_typed env Sigma(copied_array_packets env before values root dst start).
Proof.
  intros env Sigma before values root dst start attr Hbefore Hroot Hstart Hsize Hend b ofs
    [Hold|[index [delta [Hi [Hpath [Hb Hofs]]]]]].
  - apply Hbefore;exact Hold.
  - subst. pose proof(object_path_bounds _ _ _ _ Hpath) as [Hd [Hs Hins]].
    change(delta+packet_descriptor_size<=sizeof_type env root) in Hins.
    rewrite Ptrofs.unsigned_repr.
    + replace(start+Z.of_nat index*sizeof_type env root+delta)
        with(start+(Z.of_nat index*sizeof_type env root+delta)) by ring.
      eapply object_path_typing;[eapply array_path_from_index;eauto|exact Hroot].
    + pose proof packet_descriptor_size_positive;unfold Ptrofs.max_unsigned;nia.
Qed.

Theorem copied_array_scalar_coverage : forall env (values:list value) root dst start attr (cells:scalar_layout),
  (forall index delta ty chunk,(index<length values)%nat -> scalar_object_leaf env root delta ty chunk ->
    exists stored,cells dst(Ptrofs.repr(start+Z.of_nat index*sizeof_type env root+delta)) ty stored /\
      transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) ->
  forall delta ty chunk,scalar_object_leaf env(Atype root(Z.of_nat(length values)) attr) delta ty chunk ->
    exists stored,cells dst(Ptrofs.repr(start+delta)) ty stored /\
      transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Proof.
  intros env values root dst start attr cells Hcoverage delta ty chunk [Hpath Hmode].
  destruct(array_object_path_decomposition _ _ _ _ _ _ Hpath) as [[Hd Hty]|[index [relative [Hi [Hd Hchild]]]]].
  - subst;simpl in Hmode;discriminate.
  - subst delta. replace index with(Z.of_nat(Z.to_nat index)) by(rewrite Z2Nat.id;lia).
    rewrite Z.add_assoc. eapply Hcoverage;[apply Nat2Z.inj_lt;rewrite Z2Nat.id;lia|split;assumption].
Qed.

Theorem copied_array_bytes_coverage : forall env before values root dst start attr delta,
  object_path env(Atype root(Z.of_nat(length values)) attr) delta Bytes ->
  copied_array_packets env before values root dst start dst(Ptrofs.repr(start+delta)).
Proof.
  intros env before values root dst start attr delta Hpath.
  destruct(array_object_path_decomposition _ _ _ _ _ _ Hpath) as [[Hd Hty]|[index [relative [Hi [Hd Hchild]]]]];
    [discriminate|].
  right;exists(Z.to_nat index),relative. split.
  - apply Nat2Z.inj_lt;rewrite Z2Nat.id;lia.
  - split;[exact Hchild|]. split;[reflexivity|]. rewrite Z2Nat.id by lia;subst;f_equal;ring.
Qed.

Require Import BeePL_packet_alignment.

Lemma scalar_mode_natural_alignment : forall env ty cc,
  access_mode_type ty=By_value cc -> align_chunk cc=natural_object_alignment env ty.
Proof.
  intros env ty cc Hmode;destruct ty;simpl in Hmode;try discriminate.
  - destruct p;try destruct i;try destruct s;inversion Hmode;reflexivity.
  - inversion Hmode;subst;cbn [natural_object_alignment];unfold Mptr;destruct Archi.ptr64;reflexivity.
Qed.

Theorem program_fresh_array_leaf_alignment : forall p root count,
  0<=sizeof_type p.(prog_comp_env) root ->
  array_copy_leaf_alignment p.(prog_comp_env) root 0 count.
Proof.
  intros p root count Hsize index Hi;split.
  - intros delta ty chunk [Hpath Hmode]. rewrite Z.add_0_l.
    pose proof(array_path_from_index _ _ count noattr index delta ty Hi Hsize Hpath) as Hfull.
    pose proof(scalar_mode_natural_alignment p.(prog_comp_env) ty(transl_bchunk_cchunk chunk) Hmode) as Heq.
    assert(Hpower:exists n,align_chunk(transl_bchunk_cchunk chunk)=two_power_nat n).
    { rewrite Heq;apply natural_object_alignment_power. }
    exact(proj1(program_object_path_alignment _ _ _ _ Hfull
      (align_chunk(transl_bchunk_cchunk chunk)) Hpower ltac:(rewrite Heq;lia))).
  - intros delta Hpath;rewrite Z.add_0_l.
    apply (program_bytes_path_aligned p (Atype root(Z.of_nat count) noattr)).
    eapply array_path_from_index;eauto.
Qed.
