(* Complete source field lists cover scalar structs even when a field name
   occurs repeatedly: every occurrence resolves to the same declared slot. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_structure_object_coverage.
Require Import BeePL_structure_initializer_slots BeePL_structure_storage_typing.
Require Import BeePL_storage_types BeePL_runtime_locations BeePL_soundness_memory.
Require Import BeePL_layout_coherence BeePL_packet_heap BeePL_packet_state BeePL_block_extents BeePL_scalar_object_layout BeePL_soundness_store.
Require Import BeePL_auxlemmas BeePL_substitution_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma complete_scalar_struct_paths : forall env sid attr co slots,
 PTree.get sid env=Some co ->
 map scalar_field_name slots=map Ctypes.name_member
 (bmembers_cmembers(filter(fun m=>negb(member_is_padding m)) co.(co_members))) ->
 (forall slot, In slot slots -> source_member_type (scalar_field_name slot) co.(co_members)=OK(scalar_field_type slot)) ->
 (forall slot, In slot slots -> field_offset (bcomposite_composite_env env) (scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 (forall slot, In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 forall delta ty, object_path env (Stype sid attr) delta ty ->
 (delta=0 /\ ty=Stype sid attr) \/
 exists slot, In slot slots /\ delta=scalar_field_offset slot /\ ty=scalar_field_type slot.
Proof.
 intros env sid attr co slots Hco Hnames Htypes Hoffsets Hmodes delta ty Hpath.
 induction Hpath.
 - left; auto.
 - destruct IHHpath as [[Hbase Hparent]|[slot [Hin [Hbase Hparent]]]].
   + inversion Hparent; subst. assert(co0=co) by congruence; subst co0.
     assert(Hname:In field(map scalar_field_name slots)).
     { rewrite Hnames; eapply full_field_name_nonpadding; eauto. }
     apply in_map_iff in Hname; destruct Hname as [slot [Hname Hin]].
     pose proof(Htypes slot Hin) as Htype; pose proof(Hoffsets slot Hin) as Hoffset.
     rewrite Hname in Htype,Hoffset. right; exists slot; split; [exact Hin|]. split; simpl; congruence.
   + pose proof(Hmodes slot Hin) as HscalarMode; rewrite <- Hparent in HscalarMode; discriminate.
 - destruct IHHpath as [[Hbase Hparent]|[slot [Hin [Hbase Hparent]]]].
   + discriminate Hparent.
   + pose proof(Hmodes slot Hin) as HscalarMode; rewrite <- Hparent in HscalarMode; discriminate.
Qed.

Theorem complete_scalar_structure_coverage : forall env sid attr co slots (cells : scalar_layout) block,
 PTree.get sid env=Some co ->
 map scalar_field_name slots=map Ctypes.name_member
 (bmembers_cmembers(filter(fun m=>negb(member_is_padding m)) co.(co_members))) ->
 (forall slot, In slot slots -> source_member_type (scalar_field_name slot) co.(co_members)=OK(scalar_field_type slot)) ->
 (forall slot, In slot slots -> field_offset (bcomposite_composite_env env) (scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 (forall slot, In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 (forall slot, In slot slots -> cells block (Ptrofs.repr(scalar_field_offset slot)) (scalar_field_type slot)(scalar_field_chunk slot)) ->
 forall delta ty chunk, scalar_object_leaf env (Stype sid attr) delta ty chunk ->
 exists stored, cells block(Ptrofs.repr delta) ty stored /\ transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk.
Proof.
 intros * Hco Hnames Htypes Hoffsets Hmodes Hcells delta ty chunk [Hpath Hmode].
 destruct(complete_scalar_struct_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets Hmodes _ _ Hpath)
 as [[Hd Ht]|[slot [Hin [Hd Ht]]]].
 - subst ty; discriminate Hmode.
 - subst delta ty. exists(scalar_field_chunk slot); split; [apply Hcells; exact Hin|].
   pose proof(Hmodes slot Hin); congruence.
Qed.

Definition scalar_slot_expression (slot:scalar_field_slot) :=
 Val slot.(scalar_field_value) slot.(scalar_field_type).

Lemma scalar_slot_arguments : forall slots env Gamma Sigma ef ts,
 type_exprs env Gamma Sigma (map scalar_slot_expression slots) ef ts ->
 ts=map scalar_field_type slots /\
 Forall(fun slot=>type_expr env Gamma Sigma(scalar_slot_expression slot) nil(scalar_field_type slot)) slots.
Proof.
 induction slots as [|slot slots IH]; intros * Htyped; simpl in Htyped.
 - inversion Htyped; subst; split; reflexivity || constructor.
 - inversion Htyped; subst.
   match goal with Hhead:type_expr _ _ _ (scalar_slot_expression slot) _ _,
     Htail:type_exprs _ _ _ (map scalar_slot_expression slots) _ _ |- _ =>
     pose proof(type_rel_typeof _ _ _ _ _ _ Hhead) as Hty;
     pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Hhead) as Hef;
     destruct(IH _ _ _ _ _ Htail) as [Hts Hrest]
   end.
   cbn [scalar_slot_expression] in Hty. subst. split; [reflexivity|]. constructor; assumption.
Qed.

Lemma source_scalar_slot_members : forall slots members,
 source_member_types(map scalar_field_name slots) members=OK(map scalar_field_type slots) ->
 forall slot, In slot slots -> source_member_type(scalar_field_name slot) members=OK(scalar_field_type slot).
Proof.
 induction slots as [|head tail IH]; intros members Htypes slot Hin; [contradiction|].
 simpl in Htypes. unfold Errors.bind in Htypes.
 destruct(source_member_type(scalar_field_name head) members) eqn:Hhead; try discriminate.
 destruct(source_member_types(map scalar_field_name tail) members) eqn:Htail; try discriminate.
 inversion Htypes; subst. destruct Hin as [->|Hin]; [exact Hhead|eapply IH; eauto].
Qed.

Print Assumptions complete_scalar_structure_coverage.

Require Import BeePL_coherent_fields BeePL_layout_proofs.
Lemma typed_scalar_structure_slot_facts : forall p Gamma Sigma L sid attr co slots result ef,
 type_expr p.(prog_comp_env) Gamma Sigma
 (Sinit sid (map scalar_field_name slots)(map scalar_slot_expression slots) result) ef result ->
 structure_result_type sid attr result -> PTree.get sid p.(prog_comp_env)=Some co ->
 Forall(fun slot=>value_locations L (scalar_field_value slot)(scalar_field_type slot)) slots ->
 (forall slot, In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 (forall slot, In slot slots -> field_offset(bcomposite_composite_env p.(prog_comp_env))(scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 Forall(scalar_field_slot_valid p Gamma Sigma L sid attr co) slots /\
 map scalar_field_name slots=map Ctypes.name_member
 (bmembers_cmembers(filter(fun m=>negb(member_is_padding m)) co.(co_members))) /\
 (forall slot, In slot slots -> source_member_type(scalar_field_name slot) co.(co_members)=OK(scalar_field_type slot)).
Proof.
 intros * Htyped Hshape Hco Hlocations Hmodes Hoffsets.
 pose proof(typed_structure_storage_admissible _ _ _ _ _ _ _ _ _ Htyped Hshape) as Hstorage.
 inversion Htyped; subst.
 match goal with Hargs:type_exprs _ _ _ (map scalar_slot_expression slots) _ _ |- _ =>
 destruct(scalar_slot_arguments _ _ _ _ _ _ Hargs) as [Hts Hvalues] end.
 subst bts. assert(co0=co) by congruence; subst co0.
 assert(Hmembers:forall slot, In slot slots -> source_member_type(scalar_field_name slot) co.(co_members)=OK(scalar_field_type slot)).
 { eapply source_scalar_slot_members; eassumption. }
 split; [|split; assumption].
 apply Forall_forall; intros slot Hin. unfold scalar_field_slot_valid.
 split; [apply (proj1(Forall_forall _ _) Hvalues slot Hin)|].
 split; [apply (proj1(Forall_forall _ _) Hlocations slot Hin)|].
 split; [eapply storage_type_member_nonvolatile; eauto|].
 split; [|apply Hoffsets; exact Hin]. split; [|apply Hmodes; exact Hin].
 destruct(program_field_layout p id attr co (scalar_field_name slot)(scalar_field_type slot) Hco(Hmembers slot Hin))
 as [delta [Hoffset [Hlo [Hsize Hinside]]]].
 assert(delta=scalar_field_offset slot) by (pose proof(Hoffsets slot Hin); congruence); subst delta.
 replace (scalar_field_offset slot) with (0+scalar_field_offset slot) by lia.
 eapply path_field with (co:=co) (field:=scalar_field_name slot).
 - apply path_root, source_size_nonnegative.
 - exact Hco.
 - unfold Ctyping.type_of_member. rewrite(source_member_type_translation _ _ _ (Hmembers slot Hin)). reflexivity.
 - apply Hmembers; exact Hin.
 - exact Hoffset.
 - exact Hlo.
 - exact Hsize.
 - exact Hinside.
Qed.

Theorem initialize_typed_scalar_structure_fields :
 forall p Gamma Sigma L sid attr co slots result ef cells packets m block,
 type_expr p.(prog_comp_env) Gamma Sigma
 (Sinit sid (map scalar_field_name slots)(map scalar_slot_expression slots) result) ef result ->
 structure_result_type sid attr result -> PTree.get sid p.(prog_comp_env)=Some co ->
 Forall(fun slot=>value_locations L (scalar_field_value slot)(scalar_field_type slot)) slots ->
 (forall slot, In slot slots -> access_mode_type(scalar_field_type slot)=By_value(transl_bchunk_cchunk(scalar_field_chunk slot))) ->
 (forall slot, In slot slots -> field_offset(bcomposite_composite_env p.(prog_comp_env))(scalar_field_name slot)
 (bmembers_cmembers co.(co_members))=OK(scalar_field_offset slot,Full)) ->
 typed_memory_layout p.(prog_comp_env) Sigma cells m -> memory_locations L cells m -> coherent_layout cells ->
 packet_state_valid m packets -> packet_block_disjoint m packets block ->
 source_block_extent m block (sizeof_type p.(prog_comp_env)(Stype sid attr)) ->
 scalar_object_region_coherent p.(prog_comp_env) cells block 0 (Stype sid attr) ->
 exists final after,
 sem_allocate_fields (globalenv p) block Ptrofs.zero sid (map scalar_field_name slots)
 (map scalar_field_value slots)(map scalar_field_type slots) m final /\
 typed_memory_layout p.(prog_comp_env) Sigma after final /\ memory_locations L after final /\ coherent_layout after /\
 packet_state_valid final packets /\ packet_block_disjoint final packets block /\
 source_block_extent final block (sizeof_type p.(prog_comp_env)(Stype sid attr)) /\
 scalar_object_region_coherent p.(prog_comp_env) after block 0 (Stype sid attr) /\
 (forall b ofs ty chunk, cells b ofs ty chunk -> after b ofs ty chunk) /\
 (forall delta ty chunk, scalar_object_leaf p.(prog_comp_env)(Stype sid attr) delta ty chunk ->
 exists stored, after block(Ptrofs.repr delta) ty stored /\ transl_bchunk_cchunk stored=transl_bchunk_cchunk chunk) /\
 (forall b ofs ty chunk, after b ofs ty chunk -> cells b ofs ty chunk \/
 exists slot, In slot slots /\ b=block /\ ofs=Ptrofs.repr(scalar_field_offset slot) /\
 ty=scalar_field_type slot /\ chunk=scalar_field_chunk slot).
Proof.
 intros * Htyped Hshape Hco Hvalues Hmodes Hoffsets Hcells Hlocations Hcoherent Hpackets Hdisjoint Hextent Hregion.
 destruct(typed_scalar_structure_slot_facts _ _ _ _ _ _ _ _ _ _
 Htyped Hshape Hco Hvalues Hmodes Hoffsets) as [Hslots [Hnames Hmembers]].
 destruct(initialize_scalar_structure_fields slots p Gamma Sigma L sid attr co cells packets m block
 Hco Hslots Hcells Hlocations Hcoherent Hpackets Hdisjoint Hextent Hregion)
 as [final [after [Hinit [Hcells' [Hlocations' [Hcoherent' [Hpackets' [Hdisjoint' [Hextent' [Hregion' [Hold [Hcovered Horigin]]]]]]]]]]]].
 exists final,after. split; [exact Hinit|]. split; [exact Hcells'|].
 split; [exact Hlocations'|]. split; [exact Hcoherent'|]. split; [exact Hpackets'|].
 split; [exact Hdisjoint'|]. split; [exact Hextent'|]. split; [exact Hregion'|].
 split; [exact Hold|].
 split; [eapply complete_scalar_structure_coverage; eauto|exact Horigin].
Qed.

Print Assumptions initialize_typed_scalar_structure_fields.
