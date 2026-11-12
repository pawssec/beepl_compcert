(* Complete primitive initializers cover the scalar leaves of their struct.
   Full field offsets exclude bitfield padding; paths stop at primitive fields. *)
Require Import List ZArith Lia Coqlib AST Maps Memory Ctypes Integers Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_initialization_proofs BeePL_layout_proofs.
Require Import BeePL_object_paths BeePL_object_coverage BeePL_aggregate_memory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma full_field_name_nonpadding : forall members env field pos delta,
  field_offset_rec env field (bmembers_cmembers members) pos = OK (delta, Full) ->
  In field (map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) members))).
Proof.
  induction members as [|member rest IH]; intros env field pos delta H; [discriminate |].
  destruct member as [name ty | name sz sg attr width padding]; simpl in H |- *;
    destruct (ident_eq field name) as [Heq | Hneq].
  - subst field. left; reflexivity.
  - right. eapply IH; eauto.
  - unfold layout_field in H.
    destruct (zle width 0); try discriminate.
    destruct (zlt (bitsize_intsize sz) width); try discriminate.
    destruct (zle (pos + width) (floor pos (bitalignof_intsize sz) + bitalignof_intsize sz)); discriminate.
  - destruct padding; simpl; [eapply IH; eauto | right; eapply IH; eauto].
Qed.

Lemma complete_primitive_struct_paths : forall env sid attr co fs,
  PTree.get sid env = Some co ->
  map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members))) ->
  (forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))) ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env env) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  forall delta ty, object_path env (Stype sid attr) delta ty ->
    (delta = 0 /\ ty = Stype sid attr) \/
    exists f, In f fs /\ delta = planned_offset f /\ ty = Vtype (planned_type f).
Proof.
  intros env sid attr co fs Hco Hnames Htypes Hoffsets delta ty Hpath.
  induction Hpath.
  - left; auto.
  - destruct IHHpath as [[Hbase Hparent] | [f [Hin [Hbase Hparent]]]];
      [|discriminate Hparent].
    inversion Hparent; subst. assert (co0 = co) by congruence. subst co0.
    assert (Hinname : In field (map planned_field fs)).
    { rewrite Hnames. eapply full_field_name_nonpadding; eauto. }
    apply in_map_iff in Hinname. destruct Hinname as [f [Hname Hin]].
    pose proof (Htypes f Hin) as Htype. pose proof (Hoffsets f Hin) as Hoffset.
    rewrite Hname in Htype, Hoffset.
    right. exists f. split; [exact Hin |]. split; simpl; congruence.
  - destruct IHHpath as [[Hbase Hparent] | [f [Hin [Hbase Hparent]]]]; discriminate Hparent.
Qed.

Theorem primitive_structure_object_coverage :
  forall env Gamma Sigma objects cells block sid attr pointer_attr fs ef co,
  initialized_object_coverage env objects cells ->
  type_expr env Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid attr) pointer_attr))) ef
    (Ptrtype (Reftype (Bstruct sid attr) pointer_attr)) ->
  PTree.get sid env = Some co ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env env) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  initialized_object_coverage env
    (add_aggregate_descriptor objects block Ptrofs.zero (Stype sid attr))
    (extend_field_layout cells block Ptrofs.zero fs).
Proof.
  intros env Gamma Sigma objects cells block sid attr pointer_attr fs ef co
    Hcoverage Htyped Hco Hoffsets.
  destruct (typed_structure_initializer_complete _ _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [actual [Hactual [Hnames Hlength]]]].
  assert (actual = co) by congruence. subst actual.
  assert (Htypes : forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))).
  { inversion Htyped; subst.
    match goal with Hargs : type_exprs _ _ _ (planned_expressions fs) _ _ |- _ =>
      destruct (typed_planned_arguments _ _ _ _ _ _ Hargs) as [Hts Hvs]
    end.
    subst bts. assert (co0 = co) by congruence. subst co0.
    eapply source_planned_member_types; eauto. }
  intros b base root [Hold | [Hb [Hbase Hroot]]] delta ty chunk Hleaf.
  - destruct (Hcoverage _ _ _ Hold _ _ _ Hleaf) as [stored [Hcell Hchunk]].
    exists stored. split; [apply extend_field_layout_old; exact Hcell | exact Hchunk].
  - subst b base root. destruct Hleaf as [Hpath Hmode].
    destruct (complete_primitive_struct_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hpath)
      as [[Hdelta Hty] | [f [Hin [Hdelta Hty]]]].
    + subst ty. discriminate Hmode.
    + subst delta ty. exists (planned_chunk f). split.
      * rewrite Ptrofs.unsigned_zero. simpl.
        replace (Ptrofs.repr (planned_offset f)) with (planned_address Ptrofs.zero f).
        -- apply extend_field_layout_member; exact Hin.
        -- unfold planned_address. apply Ptrofs.add_zero_l.
      * pose proof (primitive_chunk_access (planned_type f)) as Haccess.
        unfold planned_chunk. congruence.
Qed.
Print Assumptions primitive_structure_object_coverage.
