(* Scalar structure-field reads: the result is the field value, not an address
   annotated with the field's scalar type. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.

Lemma scalar_field_read_progress :
  forall cenv Gamma Sigma layout bge p vm m b ofs sid sa f t co delta chunk,
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  layout b (Ptrofs.add ofs (Ptrofs.repr delta)) t chunk ->
  exists v,
    ssem_expr bge p vm m
      (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f t)
      m vm (Val v t) /\
    type_expr cenv Gamma Sigma (Val v t) nil t /\
    runtime_locations (scalar_reference_locations layout) (Val v t).
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs sid sa f t co delta chunk
    Hco Hoffset Hmemory Hlocations Hentry.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b (Ptrofs.add ofs (Ptrofs.repr delta)) t chunk
    (Hmemory _ _ _ _ Hentry)) as [v [Hread Htyped]].
  exists v. split; [eapply ssem_sfield2; eauto |].
  split; [exact Htyped |]. simpl. eapply Hlocations; eauto.
Qed.

Lemma typed_cell_not_aggregate : forall cenv Sigma m b ofs t chunk,
  typed_memory_cell cenv Sigma m b ofs t chunk ->
  (is_aggregate_type t || is_bytes t)%bool = false.
Proof.
  intros cenv Sigma m b ofs t chunk Hcell. destruct Hcell as [Hmode Hrest].
  destruct t; try reflexivity; discriminate Hmode.
Qed.

Lemma scalar_field_read_step : forall bge p vm m b ofs sid sa f t co delta m' vm' e',
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  (is_aggregate_type t || is_bytes t)%bool = false ->
  ssem_expr bge p vm m
    (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f t)
    m' vm' e' ->
  m' = m /\ vm' = vm /\ exists v,
    e' = Val v t /\ deref_addr t m b (Ptrofs.add ofs (Ptrofs.repr delta)) Full v.
Proof.
  intros bge p vm m b ofs sid sa f t co delta m' vm' e' Hco Hoffset Hscalar Hstep.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - assert (co0 = co) by congruence. subst co0.
    assert (Hfield : delta0 = delta /\ bf = Full) by (split; congruence).
    destruct Hfield as [Hd Hbf]. subst delta0 bf.
    split; [reflexivity |]. split; [reflexivity |]. eexists; split; eauto.
  - match goal with Haccess : aggregate_field_access _ _ _ _ _ _ _ _ |- _ =>
      inversion Haccess; subst
    end. congruence.
Qed.

Lemma scalar_field_read_preservation :
  forall cenv Gamma Sigma layout bge p vm m b ofs sid sa f t co delta chunk m' vm' e',
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  typed_memory_layout cenv Sigma layout m ->
  memory_locations (scalar_reference_locations layout) layout m ->
  layout b (Ptrofs.add ofs (Ptrofs.repr delta)) t chunk ->
  ssem_expr bge p vm m
    (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f t)
    m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil t /\
    runtime_locations (scalar_reference_locations layout) e'.
Proof.
  intros cenv Gamma Sigma layout bge p vm m b ofs sid sa f t co delta chunk m' vm' e'
    Hco Hoffset Hmemory Hlocations Hentry Hstep.
  assert (Hscalar : (is_aggregate_type t || is_bytes t)%bool = false)
    by (eapply typed_cell_not_aggregate; eapply Hmemory; exact Hentry).
  destruct (scalar_field_read_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hco Hoffset Hscalar Hstep)
    as [Hm [Hvm [v [He Hread]]]]. subst m' vm' e'.
  split; [reflexivity |]. split; [reflexivity |]. split.
  - eapply typed_memory_cell_read_preservation; eauto.
  - simpl. eapply Hlocations; eauto.
Qed.

Print Assumptions scalar_field_read_progress.
Print Assumptions scalar_field_read_step.
Print Assumptions scalar_field_read_preservation.

Lemma scalar_field_big_step_result :
  forall cenv Gamma Sigma layout bge p vm m e m' vm' b ofs sid sa f t co delta chunk,
  bsem_expr bge p vm m e m' vm' (Vloc b ofs) ->
  typeof_expr e = Ptrtype (Reftype (Bstruct sid sa) noattr) ->
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  typed_memory_layout cenv Sigma layout m' ->
  memory_locations (scalar_reference_locations layout) layout m' ->
  layout b (Ptrofs.add ofs (Ptrofs.repr delta)) t chunk ->
  exists v, bsem_expr bge p vm m (Sfield e f t) m' vm' v /\
    type_expr cenv Gamma Sigma (Val v t) nil t /\
    runtime_locations (scalar_reference_locations layout) (Val v t).
Proof.
  intros cenv Gamma Sigma layout bge p vm m e m' vm' b ofs sid sa f t co delta chunk
    Hbase Hbase_type Hco Hoffset Hmemory Hlocations Hentry.
  destruct (typed_memory_cell_read cenv Gamma Sigma m' b (Ptrofs.add ofs (Ptrofs.repr delta)) t chunk
    (Hmemory _ _ _ _ Hentry)) as [v [Hread Htyped]].
  exists v. split; [eapply bsem_sfield; eauto |].
  split; [exact Htyped |]. simpl. eapply Hlocations; eauto.
Qed.

(* Regression: an integer field step returns an integer payload, never the
   field's address mislabeled as an integer. *)
Lemma integer_field_result :
  forall cenv Sigma layout bge p vm m b ofs sid sa f sz sign attr co delta chunk m' vm' e',
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  typed_memory_layout cenv Sigma layout m ->
  layout b (Ptrofs.add ofs (Ptrofs.repr delta)) (Vtype (Tint sz sign attr)) chunk ->
  ssem_expr bge p vm m
    (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f (Vtype (Tint sz sign attr)))
    m' vm' e' ->
  exists i, e' = Val (Vint i) (Vtype (Tint sz sign attr)).
Proof.
  intros cenv Sigma layout bge p vm m b ofs sid sa f sz sign attr co delta chunk m' vm' e'
    Hco Hoffset Hmemory Hentry Hstep.
  assert (Hscalar : (is_aggregate_type (Vtype (Tint sz sign attr)) || is_bytes (Vtype (Tint sz sign attr)))%bool = false)
    by reflexivity.
  destruct (scalar_field_read_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hco Hoffset Hscalar Hstep)
    as [Hm [Hvm [v [He Hread]]]]. subst e'.
  pose proof (typed_memory_cell_read_preservation cenv empty_context Sigma m b
    (Ptrofs.add ofs (Ptrofs.repr delta)) (Vtype (Tint sz sign attr)) chunk v
    (Hmemory _ _ _ _ Hentry) Hread) as Htyped.
  inversion Htyped; subst. eexists; reflexivity.
Qed.

Print Assumptions scalar_field_big_step_result.
Print Assumptions integer_field_result.

Require Import Lia.
Local Open Scope Z_scope.

Lemma aggregate_field_access_layout :
  forall cenv Sigma m b ofs base_type f ty result,
  aggregate_field_access cenv m b ofs base_type f ty result ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    object_type_at cenv Sigma b (Ptrofs.unsigned ofs) (Stype sid attr)) ->
  object_type_at cenv Sigma b (Ptrofs.unsigned result) ty.
Proof.
  intros cenv Sigma m b ofs base_type f ty result Haccess Hbase.
  inversion Haccess; subst. rewrite Ptrofs.unsigned_repr.
  - eapply object_type_field; eauto.
  - pose proof (Ptrofs.unsigned_range ofs). lia.
Qed.

Lemma aggregate_field_access_typed_result :
  forall cenv Gamma Sigma m b ofs base_type f ty result,
  aggregate_field_access cenv m b ofs base_type f ty result ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    object_type_at cenv Sigma b (Ptrofs.unsigned ofs) (Stype sid attr)) ->
  type_expr cenv Gamma Sigma (Val (Vloc b result) ty) nil ty.
Proof.
  intros cenv Gamma Sigma m b ofs base_type f ty result Haccess Hbase.
  pose proof (aggregate_field_access_layout _ _ _ _ _ _ _ _ _ Haccess Hbase) as Hlayout.
  assert (Haggregate : (is_aggregate_type ty || is_bytes ty)%bool = true) by (inversion Haccess; assumption).
  destruct ty; simpl in Haggregate; try discriminate; constructor; exact Hlayout.
Qed.

Lemma aggregate_field_value_progress :
  forall bge p Gamma Sigma vm m b ofs base_type f ty result,
  aggregate_field_access bge.(genv_cenv) m b ofs base_type f ty result ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    object_type_at bge.(genv_cenv) Sigma b (Ptrofs.unsigned ofs) (Stype sid attr)) ->
  ssem_expr bge p vm m (Sfield (Val (Vloc b ofs) base_type) f ty)
    m vm (Val (Vloc b result) ty) /\
  type_expr bge.(genv_cenv) Gamma Sigma (Val (Vloc b result) ty) nil ty.
Proof.
  intros. split; [apply ssem_sfield_aggregate; assumption |].
  eapply aggregate_field_access_typed_result; eassumption.
Qed.

Lemma aggregate_full_deref_impossible : forall ty m b ofs v,
  is_aggregate_type ty = true ->
  ~ deref_addr ty m b ofs Full v.
Proof.
  intros ty m b ofs v Haggregate Hread.
  inversion Hread; subst; simpl in Haggregate; try discriminate;
    destruct ty; simpl in Haggregate; try discriminate;
    match goal with Hmode : access_mode_type _ = _ |- _ => discriminate Hmode end.
Qed.

Theorem aggregate_field_value_preservation :
  forall bge p Gamma Sigma vm m b ofs base_type f ty m' vm' e',
  is_aggregate_type ty = true ->
  (forall sid attr, base_type = Stype sid attr \/
    base_type = Ptrtype (Reftype (Bstruct sid attr) noattr) ->
    object_type_at bge.(genv_cenv) Sigma b (Ptrofs.unsigned ofs) (Stype sid attr)) ->
  ssem_expr bge p vm m (Sfield (Val (Vloc b ofs) base_type) f ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr bge.(genv_cenv) Gamma Sigma e' nil ty.
Proof.
  intros bge p Gamma Sigma vm m b ofs base_type f ty m' vm' e' Haggregate Hbase Hstep.
  inversion Hstep; subst.
  - exfalso; eapply value_has_no_small_step; eauto.
  - match goal with Hread : deref_addr _ _ _ _ ?bf _ |- _ =>
      destruct bf; inversion Hread; subst; simpl in Haggregate; try discriminate;
      destruct ty; simpl in Haggregate; try discriminate
    end.
    all: try solve [first
      [ match goal with Hmode : access_mode_type _ = _ |- _ => discriminate Hmode end
      | match goal with Hload : Cop.load_bitfield _ _ _ _ _ _ _ _ |- _ => inversion Hload end ]].
  - match goal with Hread : deref_addr _ _ _ _ ?bf _ |- _ =>
      destruct bf; inversion Hread; subst; simpl in Haggregate; try discriminate;
      destruct ty; simpl in Haggregate; try discriminate
    end.
    all: try solve [first
      [ match goal with Hmode : access_mode_type _ = _ |- _ => discriminate Hmode end
      | match goal with Hload : Cop.load_bitfield _ _ _ _ _ _ _ _ |- _ => inversion Hload end ]].
  - split; [reflexivity |]. split; [reflexivity |].
    eapply aggregate_field_access_typed_result; eauto.
Qed.

Print Assumptions aggregate_field_access_layout.
Print Assumptions aggregate_field_access_typed_result.
Print Assumptions aggregate_field_value_progress.
Print Assumptions aggregate_field_value_preservation.

Require Import BeePL_layout_proofs.

Theorem aggregate_field_access_from_layout :
  forall cenv Sigma m b ofs base_type f ty sid attr co cty delta stored,
  (base_type = Stype sid attr \/ base_type = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  object_type_at cenv Sigma b (Ptrofs.unsigned ofs) (Stype sid attr) ->
  PTree.get sid cenv = Some co ->
  Ctyping.type_of_member attr f (bmembers_cmembers co.(co_members)) = OK cty ->
  source_member_type f co.(co_members) = OK ty ->
  field_offset (bcomposite_composite_env cenv) f (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  (is_aggregate_type ty || is_bytes ty)%bool = true ->
  0 <= delta -> 0 <= sizeof_type cenv ty ->
  delta + sizeof_type cenv ty <= sizeof_type cenv (Stype sid attr) ->
  PTree.get b Sigma = Some stored ->
  sizeof_type cenv (stored_object_type stored) <= Ptrofs.max_unsigned ->
  Mem.valid_block m b ->
  Mem.range_perm m b 0 (sizeof_type cenv (stored_object_type stored)) Cur Readable ->
  aggregate_field_access cenv m b ofs base_type f ty
    (Ptrofs.repr (Ptrofs.unsigned ofs + delta)).
Proof.
  intros cenv Sigma m b ofs base_type f ty sid attr co cty delta stored
    Hbase_type Hbase Hco Hmember Htranslation Hoffset Haggregate Hdelta Hsize Hwithin
    Hstored Hrepresentable Hvalid Hread.
  assert (Hchild : object_type_at cenv Sigma b (Ptrofs.unsigned ofs + delta) ty).
  { eapply object_type_field; eauto. }
  destruct (object_type_at_within_allocation _ _ _ _ _ Hchild)
    as [root [Hroot [Hchild_offset [Hchild_size Hbound]]]].
  assert (root = stored) by congruence. subst root.
  eapply aggregate_field_access_intro; eauto; try lia.
  eapply object_type_at_readable_subrange; eassumption.
Qed.

Print Assumptions aggregate_field_access_from_layout.
