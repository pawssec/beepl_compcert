(* Header layouts cover declared primitive leaves, including unbound fields.
   Attribute alignment comes from the accepted program builder, not a noattr
   premise imposed on packet fields. *)
Require Import List Bool ZArith Lia Integers AST Maps Memory Memdata Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_packet BeePL_packet_proofs BeePL_packet_schema_check BeePL_storage_types.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_object_paths.
Require Import BeePL_object_coverage BeePL_aggregate_memory BeePL_packet_alignment.
Require Import BeePL_layout_proofs BeePL_array_proofs BeePL_structure_object_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Lemma safe_packet_schema_shape : forall env sid fields,
  storage_safe_packet_schema env sid fields -> packet_schema_valid env sid fields.
Proof. intros env sid fields [co [Hg [Hs [Hm [Hf Hstorage]]]]]. exists co; auto. Qed.

Lemma primitive_member_source_packet : forall members,
  Forall (fun member => exists name pt, member=Member_plain name(Vtype pt)) members ->
  forall name ty, source_member_type name members=OK ty ->
  exists pt, ty=Vtype pt /\ packet_member_type name members=Some(Vtype pt).
Proof.
  intros members Hmembers. induction Hmembers as [|member rest Hmember Hrest IH];
    intros name ty Hsource; [discriminate|].
  destruct Hmember as [field [pt ->]]. simpl in Hsource |- *.
  destruct (ident_eq name field); [inversion Hsource; subst; eauto|]. eapply IH; eauto.
Qed.

Lemma primitive_schema_object_paths : forall env sid attr co,
  PTree.get sid env=Some co ->
  Forall (fun member => exists name pt, member=Member_plain name(Vtype pt)) (co_members co) ->
  forall delta ty, object_path env(Stype sid attr) delta ty ->
    (delta=0 /\ ty=Stype sid attr) \/
    exists name pt, ty=Vtype pt /\ packet_member_type name(co_members co)=Some(Vtype pt) /\
      field_offset (bcomposite_composite_env env) name(bmembers_cmembers(co_members co))=OK(delta,Full).
Proof.
  intros env sid attr co Hco Hmembers delta ty Hpath. induction Hpath.
  - left; auto.
  - destruct IHHpath as [[Hbase Hparent]|[name [pt [Hparent Hrest]]]]; [|discriminate].
    inversion Hparent; subst. assert(co0=co) by congruence. subst co0.
    match goal with Hmember : source_member_type field (co_members co) = OK ty |- _ =>
      destruct (primitive_member_source_packet _ Hmembers _ _ Hmember) as [pt [Hty Hpacket]] end.
    right. exists field,pt. subst ty. repeat split; auto.
  - destruct IHHpath as [[Hbase Hparent]|[name [pt [Hparent Hrest]]]]; discriminate.
Qed.

Theorem packet_header_object_coverage : forall env objects cells fresh sid co,
  initialized_object_coverage env objects cells -> PTree.get sid env=Some co ->
  Forall (fun member => exists name pt, member=Member_plain name(Vtype pt)) (co_members co) ->
  initialized_object_coverage env
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells env co fresh).
Proof.
  intros env objects cells fresh sid co Hcoverage Hco Hmembers b base root Hobject delta ty chunk [Hpath Hmode].
  destruct Hobject as [Hold|[Hb [Hbase Hroot]]].
  - destruct (Hcoverage _ _ _ Hold _ _ _ (conj Hpath Hmode)) as [stored [Hcell Heq]].
    exists stored; split; [left; exact Hcell|exact Heq].
  - subst b base root.
    destruct (primitive_schema_object_paths _ _ _ _ Hco Hmembers _ _ Hpath)
      as [[Hdelta Hty]|[name [pt [Hty [Hlookup Hoffset]]]]]; [subst ty; discriminate|].
    subst ty. exists (chunk_of_ptype pt). split.
    + right. exists name,pt,delta. rewrite Ptrofs.unsigned_zero; simpl. repeat split; auto.
    + pose proof (primitive_chunk_access pt) as Hcanonical. congruence.
Qed.

Theorem safe_prepared_packet_header_cells : forall p Sigma Sigma' cells sid fields co m bytes final fresh,
  storage_safe_packet_schema p.(prog_comp_env) sid fields ->
  PTree.get sid p.(prog_comp_env)=Some co ->
  Z.of_nat(List.length bytes)=co_sizeof co -> initialized_packet_contents bytes ->
  prepare_packet_header (bcomposite_composite_env p.(prog_comp_env)) (co_members co) m bytes=OK(final,fresh) ->
  typed_memory_layout p.(prog_comp_env) Sigma cells m -> store_context_extends Sigma Sigma' ->
  typed_memory_layout p.(prog_comp_env) Sigma' (packet_header_layout cells p.(prog_comp_env) co fresh) final.
Proof.
  intros p Sigma Sigma' cells sid fields co m bytes final fresh Hsafe Hco Hsize Hinit Hprepare Hmemory Hext b ofs ty chunk Hcell.
  destruct Hcell as [Hold|[name [pt [delta [Hb [Hofs [Hty [Hchunk [Hlookup Hoffset]]]]]]]]].
  - eapply typed_memory_layout_unchanged_old; [exact Hmemory|exact Hext| |exact Hold].
    eapply prepare_packet_header_unchanged_old; exact Hprepare.
  - subst b ofs ty chunk.
    destruct Hsafe as [actual [Hactual [Hstruct [Hmembers [Hfields Hstorage]]]]].
    assert(actual=co) by congruence; subst actual.
    eapply prepared_packet_field_cell; eauto.
    + exists co; auto.
    + exact (program_composites_consistent p sid co Hco).
    + pose proof (storage_type_size_bounds _ _ Hstorage) as Hbound.
      simpl in Hbound; rewrite Hco in Hbound; exact (proj2 Hbound).
    + pose proof (proj2 (program_field_natural_alignment p sid noattr co name (Vtype pt) delta
        Hco (packet_member_type_source _ _ _ Hlookup) Hoffset)) as Halign.
      change (alignof_ptype pt | delta) in Halign.
      replace (align_chunk (transl_bchunk_cchunk(chunk_of_ptype pt))) with (alignof_ptype pt);
        [exact Halign|]. destruct pt as [|sz sign attr|sign attr]; try destruct sz; try destruct sign; reflexivity.
    + eapply storage_type_member_nonvolatile; [exact Hstorage|exact Hco|].
      eapply packet_member_type_source; exact Hlookup.
Qed.

Require Import BeePL_coherent_fields BeePL_initializer_coherence BeePL_object_separation.
Require Import BeePL_scalar_object_layout.

Lemma packet_header_declared_leaf : forall p sid co name pt delta,
  PTree.get sid p.(prog_comp_env)=Some co -> co_sizeof co <= Ptrofs.max_unsigned ->
  packet_member_type name (co_members co)=Some(Vtype pt) ->
  field_offset (bcomposite_composite_env p.(prog_comp_env)) name
    (bmembers_cmembers(co_members co))=OK(delta,Full) ->
  scalar_object_leaf p.(prog_comp_env) (Stype sid noattr)
    (Ptrofs.unsigned(Ptrofs.repr delta)) (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros p sid co name pt delta Hco Hbound Hmember Hoffset.
  pose proof (packet_member_type_source _ _ _ Hmember) as Hsource.
  destruct (program_field_layout p sid noattr co name (Vtype pt) Hco Hsource)
    as [actual [Hactual [Hlo [Hsize Hwithin]]]].
  assert(actual=delta) by congruence; subst actual.
  assert(Hrange:0<=delta<=Ptrofs.max_unsigned).
  { simpl in Hwithin, Hsize. rewrite Hco in Hwithin. lia. }
  rewrite Ptrofs.unsigned_repr by exact Hrange. split; [|apply primitive_chunk_access].
  replace delta with (0+delta) by lia. eapply path_field; eauto.
  - constructor. apply object_source_size_nonnegative.
  - unfold Ctyping.type_of_member. rewrite (packet_member_type_translation _ _ _ Hmember). reflexivity.
Qed.

Theorem packet_header_scalar_object_coherence : forall p Sigma m objects cells sid co allocated fresh,
  aggregate_objects_valid p.(prog_comp_env) Sigma m objects ->
  typed_memory_layout p.(prog_comp_env) Sigma cells m ->
  scalar_object_coherence p.(prog_comp_env) objects cells ->
  PTree.get sid p.(prog_comp_env)=Some co -> co_sizeof co <= Ptrofs.max_unsigned ->
  Mem.alloc m 0(co_sizeof co)=(allocated,fresh) ->
  scalar_object_coherence p.(prog_comp_env)
    (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid noattr))
    (packet_header_layout cells p.(prog_comp_env) co fresh).
Proof.
  intros p Sigma m objects cells sid co allocated fresh Hobjects Hmemory Hcoherent Hco Hbound Halloc.
  eapply fresh_declared_initializer_coherence; [exact Hobjects|exact Hmemory|exact Hcoherent| | |].
  - simpl; rewrite Hco; exact Halloc.
  - intros delta ty chunk Hleaf childoffset child Hpath.
    eapply program_scalar_leaf_subobject; eauto.
  - intros b ofs ty chunk [Hold|[name [pt [delta [Hb [Hofs [Hty [Hchunk [Hmember Hoffset]]]]]]]]]; [auto|].
    subst b ofs ty chunk. right; split; [reflexivity|].
    eapply packet_header_declared_leaf; eauto.
Qed.
