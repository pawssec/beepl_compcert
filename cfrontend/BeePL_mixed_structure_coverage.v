(* Every non-root path of a complete source struct belongs to one of the
   initialized fields. Nested arrays/structs and Bytes stay supported. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_structure_object_coverage BeePL_soundness_memory.
Require Import BeePL_structure_field_planning BeePL_mixed_structure_fields.
Import ListNotations.
Local Open Scope Z_scope.

Lemma complete_mixed_structure_paths : forall env sid attr co fields,
 PTree.get sid env=Some co ->
 map field_slot_name fields=map Ctypes.name_member
 (bmembers_cmembers(filter(fun member=>negb(member_is_padding member)) co.(co_members))) ->
 (forall field,In field fields ->source_member_type(field_slot_name field) co.(co_members)=OK(field_slot_type field)) ->
 (forall field,In field fields ->field_offset(bcomposite_composite_env env)(field_slot_name field)
 (bmembers_cmembers co.(co_members))=OK(field_slot_offset field,Full)) ->
 forall delta ty,object_path env(Stype sid attr) delta ty ->
 (delta=0 /\ty=Stype sid attr) \/
 exists field relative,In field fields /\object_path env(field_slot_type field) relative ty /\delta=field_slot_offset field+relative.
Proof.
 intros * Hco Hnames Htypes Hoffsets delta ty Hpath;induction Hpath.
 - left;auto.
 - destruct IHHpath as [[Hb Hparent]|[slot [relative [Hin [Hsub Heq]]]]].
   + inversion Hparent;subst. assert(co0=co) by congruence;subst co0.
     assert(Hname:In field(map field_slot_name fields)).
     { rewrite Hnames;eapply full_field_name_nonpadding;eauto. }
     apply in_map_iff in Hname;destruct Hname as [slot [Hname Hin]].
     pose proof(Htypes slot Hin) as Htype;pose proof(Hoffsets slot Hin) as Hoffset.
     rewrite Hname in Htype,Hoffset.
     assert(ty=field_slot_type slot) by congruence;subst ty.
     assert(delta=field_slot_offset slot) by congruence;subst delta.
     right;exists slot,0;split;[exact Hin|]. split;[constructor;assumption|lia].
   + right;exists slot,(relative+delta);split;[exact Hin|]. split;[|lia].
     eapply path_field;[exact Hsub|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption|eassumption].
 - destruct IHHpath as [[Hb Hparent]|[slot [relative [Hin [Hsub Heq]]]]].
   + discriminate Hparent.
   + right;exists slot,(relative+index*sizeof_type env ty);split;[exact Hin|]. split;[|lia].
     eapply path_array_element;eauto.
Qed.

Theorem complete_mixed_structure_scalar_coverage : forall env sid attr co fields (cells:scalar_layout) dst,
 PTree.get sid env=Some co ->
 map field_slot_name fields=map Ctypes.name_member
 (bmembers_cmembers(filter(fun member=>negb(member_is_padding member)) co.(co_members))) ->
 (forall field,In field fields ->source_member_type(field_slot_name field) co.(co_members)=OK(field_slot_type field)) ->
 (forall field,In field fields ->field_offset(bcomposite_composite_env env)(field_slot_name field)
 (bmembers_cmembers co.(co_members))=OK(field_slot_offset field,Full)) ->
 Forall(field_scalar_coverage env cells dst) fields ->
 forall delta ty chunk,scalar_object_leaf env(Stype sid attr) delta ty chunk ->
 exists stored,cells dst(Ptrofs.repr delta) ty stored /\transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Proof.
 intros * Hco Hnames Htypes Hoffsets Hcoverage delta ty chunk [Hpath Hmode].
 destruct(complete_mixed_structure_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hpath)
 as [[Hd Ht]|[field [relative [Hin [Hsub Heq]]]]].
 - subst ty;discriminate Hmode.
 - rewrite Heq;apply(proj1(Forall_forall _ _) Hcoverage field Hin);split;assumption.
Qed.

Theorem complete_mixed_structure_packet_coverage : forall env sid attr co fields packets dst,
 PTree.get sid env=Some co ->
 map field_slot_name fields=map Ctypes.name_member
 (bmembers_cmembers(filter(fun member=>negb(member_is_padding member)) co.(co_members))) ->
 (forall field,In field fields ->source_member_type(field_slot_name field) co.(co_members)=OK(field_slot_type field)) ->
 (forall field,In field fields ->field_offset(bcomposite_composite_env env)(field_slot_name field)
 (bmembers_cmembers co.(co_members))=OK(field_slot_offset field,Full)) ->
 Forall(field_packet_coverage env packets dst) fields ->
 forall delta,object_path env(Stype sid attr) delta Bytes ->packets dst(Ptrofs.repr delta).
Proof.
 intros * Hco Hnames Htypes Hoffsets Hcoverage delta Hpath.
 destruct(complete_mixed_structure_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hpath)
 as [[Hd Ht]|[field [relative [Hin [Hsub Heq]]]]];[discriminate Ht|].
 rewrite Heq;apply(proj1(Forall_forall _ _) Hcoverage field Hin);exact Hsub.
Qed.
