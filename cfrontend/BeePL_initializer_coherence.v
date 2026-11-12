(* Generated primitive initializer cells are declared leaves. Fresh allocation
   separates them from the old heap; static paths control every subobject. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_scalar_object_layout.
Require Import BeePL_array_proofs BeePL_array_object_coverage.
Require Import BeePL_layout_proofs.
Require Import BeePL_initialization_proofs BeePL_structure_copy_layout BeePL_structure_object_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Definition declared_leaf_separation env root : Prop :=
  forall cell_delta ty chunk, scalar_object_leaf env root cell_delta ty chunk ->
  forall child_delta child, object_path env root child_delta child ->
  (cell_delta + size_chunk (transl_bchunk_cchunk chunk) <= child_delta \/
   child_delta + sizeof_type env child <= cell_delta) \/
  exists relative, scalar_object_leaf env child relative ty chunk /\
    cell_delta = child_delta + relative.

Lemma fresh_declared_initializer_coherence :
  forall env Sigma m objects cells fresh allocated root (after : scalar_layout),
  aggregate_objects_valid env Sigma m objects -> typed_memory_layout env Sigma cells m ->
  scalar_object_coherence env objects cells ->
  Mem.alloc m 0 (sizeof_type env root) = (allocated,fresh) ->
  declared_leaf_separation env root ->
  (forall b ofs ty chunk, after b ofs ty chunk -> cells b ofs ty chunk \/
    (b=fresh /\ scalar_object_leaf env root (Ptrofs.unsigned ofs) ty chunk)) ->
  scalar_object_coherence env (add_aggregate_descriptor objects fresh Ptrofs.zero root) after.
Proof.
  intros env Sigma m objects cells fresh allocated root after Hobjects Hmemory Hcoherent Ha Hseparation Horigin.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ Ha) as Hfresh.
  intros b base object Hobject delta child Hpath block ofs ty chunk Hcell.
  destruct Hobject as [HoldObject|[Hb [Hbase Hroot]]];
    destruct (Horigin _ _ _ _ Hcell) as [HoldCell|[Hblock Hleaf]].
  - eapply Hcoherent; eauto.
  - subst block. left; left. intro Heq; subst b. apply Hfresh.
    destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ HoldObject)
      as [_ [_ [_ [Hvalid _]]]]. exact Hvalid.
  - subst b. left; left. intro Heq; subst block. apply Hfresh.
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. eapply Hmemory; exact HoldCell.
  - subst b base object block. rewrite Ptrofs.unsigned_zero, Z.add_0_l.
    destruct (Hseparation _ _ _ Hleaf _ _ Hpath) as [Hapart|[relative [Hrelative Hposition]]].
    + left; right; exact Hapart.
    + right; exists relative. split; [exact Hrelative|]. split; [reflexivity|exact Hposition].
Qed.

Lemma primitive_array_leaf_separation : forall env pt count attr,
  declared_leaf_separation env (Atype (Vtype pt) (Z.of_nat count) attr).
Proof.
  intros env pt count attr cell_delta ty chunk Hleaf child_delta child Hpath.
  pose proof Hleaf as HleafOriginal.
  destruct (primitive_array_scalar_leaf _ _ _ _ _ _ _ Hleaf)
    as [index [Hindex [Hcell [Hty Hchunk]]]]. subst cell_delta ty.
  destruct (primitive_array_object_paths _ _ _ _ _ _ Hpath)
    as [[Hzero Hroot]|[other [Hother [Hdelta Hchild]]]].
  - subst child_delta child. right; exists (index * sizeof_ptype pt). split; [exact HleafOriginal|lia].
  - subst child_delta child. destruct (Z.eq_dec index other) as [Heq|Hneq].
    + subst other. right; exists 0. split; [|lia]. split.
      * apply path_root. simpl. pose proof (primitive_size_positive pt); lia.
      * destruct HleafOriginal; assumption.
    + left. rewrite Hchunk, primitive_chunk_size. simpl.
      pose proof (primitive_size_positive pt). nia.
Qed.

Theorem primitive_array_initializer_coherence :
  forall env Sigma m objects cells fresh allocated pt count attr,
  aggregate_objects_valid env Sigma m objects -> typed_memory_layout env Sigma cells m ->
  scalar_object_coherence env objects cells ->
  Mem.alloc m 0 (sizeof_type env (Atype (Vtype pt) (Z.of_nat count) attr)) = (allocated,fresh) ->
  sizeof_ptype pt * Z.of_nat count <= Ptrofs.max_unsigned ->
  scalar_object_coherence env
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) (Z.of_nat count) attr))
    (extend_array_layout cells fresh pt count).
Proof.
  intros env Sigma m objects cells fresh allocated pt count attr Hobjects Hmemory Hcoherent Ha Hsize.
  eapply fresh_declared_initializer_coherence; [exact Hobjects|exact Hmemory|exact Hcoherent|exact Ha|
    apply primitive_array_leaf_separation|].
  intros b ofs ty chunk [Hold|[index [Hindex [Hb [Hofs [Hty Hchunk]]]]]]; [left; exact Hold|].
  subst b ofs ty chunk. right; split; [reflexivity|].
  apply Nat2Z.inj_lt in Hindex. pose proof (primitive_size_positive pt) as Hwidth.
  rewrite Ptrofs.unsigned_repr by nia. split; [|apply primitive_chunk_access].
  replace (Z.of_nat index * sizeof_ptype pt) with (0 + Z.of_nat index * sizeof_type env (Vtype pt)) by reflexivity.
  eapply path_array_element; [apply path_root; simpl; nia|lia|simpl; lia].
Qed.

Lemma initializer_field_members_separated : forall fs base f g,
  field_plans_separated base fs -> In f fs -> In g fs ->
  f=g \/ planned_end base f <= planned_start base g \/ planned_end base g <= planned_start base f.
Proof.
  induction fs as [|head rest IH]; intros base f g Hsep Hf Hg; [contradiction|].
  destruct Hsep as [Hhead Hrest]. destruct Hf as [<-|Hf]; destruct Hg as [<-|Hg].
  - left; reflexivity.
  - right; eauto.
  - right; destruct (Hhead f Hf); auto.
  - eapply IH; eauto.
Qed.

Lemma initializer_planned_start : forall f,
  0 <= planned_offset f <= Ptrofs.max_unsigned ->
  planned_start Ptrofs.zero f = planned_offset f.
Proof.
  intros f H. unfold planned_start, planned_address.
  rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; auto.
Qed.

Lemma primitive_structure_leaf_separation : forall env sid attr co fs,
  PTree.get sid env = Some co ->
  map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members))) ->
  (forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))) ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env env) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  (forall f, In f fs -> 0 <= planned_offset f <= Ptrofs.max_unsigned) ->
  field_plans_separated Ptrofs.zero fs ->
  declared_leaf_separation env (Stype sid attr).
Proof.
  intros env sid attr co fs Hco Hnames Htypes Hoffsets Hbounds Hseparated
    cell_delta ty chunk [Hcell Hmode] child_delta child Hchild.
  pose proof Hcell as HcellOriginal.
  destruct (complete_primitive_struct_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hcell)
    as [[Hdelta Hty]|[f [Hin [Hdelta Hty]]]]; [subst ty; discriminate Hmode|].
  subst cell_delta ty.
  destruct (complete_primitive_struct_paths _ _ _ _ _ Hco Hnames Htypes Hoffsets _ _ Hchild)
    as [[Hzero Hroot]|[g [Hgin [Hgdelta Hgty]]]].
  - subst child_delta child. right; exists (planned_offset f). split; [split; assumption|lia].
  - subst child_delta child.
    destruct (initializer_field_members_separated _ _ _ _ Hseparated Hin Hgin) as [Heq|Hapart].
    + subst g. right; exists 0. split; [|lia]. split; [|exact Hmode].
      apply path_root. simpl. pose proof (primitive_size_positive (planned_type f)); lia.
    + left. unfold planned_end in Hapart.
      rewrite (initializer_planned_start f (Hbounds f Hin)),
        (initializer_planned_start g (Hbounds g Hgin)) in Hapart.
      assert (Hchunk : transl_bchunk_cchunk chunk = transl_bchunk_cchunk (planned_chunk f)).
      { unfold planned_chunk. rewrite primitive_chunk_access in Hmode. congruence. }
      rewrite Hchunk. simpl. unfold planned_chunk in *.
      rewrite !primitive_chunk_size in *. exact Hapart.
Qed.

Theorem primitive_structure_initializer_coherence :
  forall env Sigma m objects cells fresh allocated sid attr co fs,
  aggregate_objects_valid env Sigma m objects -> typed_memory_layout env Sigma cells m ->
  scalar_object_coherence env objects cells ->
  PTree.get sid env = Some co -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  map planned_field fs = map Ctypes.name_member
    (bmembers_cmembers (filter (fun m => negb (BeeTypes.member_is_padding m)) co.(co_members))) ->
  (forall f, In f fs -> source_member_type (planned_field f) co.(co_members) = OK (Vtype (planned_type f))) ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env env) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  (forall f, In f fs -> 0 <= planned_offset f /\
    planned_offset f + sizeof_ptype (planned_type f) <= co.(co_sizeof)) ->
  field_plans_separated Ptrofs.zero fs ->
  Mem.alloc m 0 (sizeof_type env (Stype sid attr)) = (allocated,fresh) ->
  scalar_object_coherence env
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
    (extend_field_layout cells fresh Ptrofs.zero fs).
Proof.
  intros env Sigma m objects cells fresh allocated sid attr co fs Hobjects Hmemory Hcoherent
    Hco Hsize Hnames Htypes Hoffsets Hbounds Hseparated Ha.
  assert (Hrepresentable : forall f, In f fs -> 0 <= planned_offset f <= Ptrofs.max_unsigned).
  { intros f Hin. specialize (Hbounds f Hin). pose proof (primitive_size_positive (planned_type f)); lia. }
  eapply fresh_declared_initializer_coherence; [exact Hobjects|exact Hmemory|exact Hcoherent|exact Ha| |].
  - eapply primitive_structure_leaf_separation; eauto.
  - intros b ofs ty chunk Hcell.
    destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hcell)
      as [Hold|[f [Hin [Hb [Hofs [Hty Hchunk]]]]]]; [left; exact Hold|].
    subst b ofs ty chunk. right; split; [reflexivity|].
    change (scalar_object_leaf env (Stype sid attr) (planned_start Ptrofs.zero f)
      (Vtype (planned_type f)) (planned_chunk f)).
    rewrite initializer_planned_start by (apply Hrepresentable; exact Hin).
    split; [|apply primitive_chunk_access].
    replace (planned_offset f) with (0 + planned_offset f) at 1 by lia.
    eapply path_field with (co := co) (field := planned_field f).
    + apply path_root. simpl. rewrite Hco. pose proof (co_sizeof_pos co); lia.
    + exact Hco.
    + unfold Ctyping.type_of_member. rewrite (source_member_type_translation _ _ _ (Htypes f Hin)). reflexivity.
    + exact (Htypes f Hin).
    + exact (Hoffsets f Hin).
    + exact (proj1 (Hbounds f Hin)).
    + simpl. pose proof (primitive_size_positive (planned_type f)); lia.
    + simpl. rewrite Hco. exact (proj2 (Hbounds f Hin)).
Qed.

Print Assumptions primitive_array_initializer_coherence.
Print Assumptions primitive_structure_initializer_coherence.

Require Import BeePL_object_separation BeePL_structure_storage_typing.

Theorem program_primitive_structure_initializer_coherence :
  forall p Gamma Sigma m objects cells fresh allocated sid attr co fs result ef,
  aggregate_objects_valid p.(prog_comp_env) Sigma m objects ->
  typed_memory_layout p.(prog_comp_env) Sigma cells m ->
  scalar_object_coherence p.(prog_comp_env) objects cells ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_offset (bcomposite_composite_env p.(prog_comp_env)) (planned_field f)
    (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid attr)) = (allocated,fresh) ->
  scalar_object_coherence p.(prog_comp_env)
    (add_aggregate_descriptor objects fresh Ptrofs.zero (Stype sid attr))
    (extend_field_layout cells fresh Ptrofs.zero fs).
Proof.
  intros p Gamma Sigma m objects cells fresh allocated sid attr co fs result ef
    Hobjects Hmemory Hcoherent Htyped Hco Hsize Hoffsets Ha.
  assert (Htypes : forall f, In f fs -> source_member_type (planned_field f)
    co.(co_members) = OK (Vtype (planned_type f))).
  { eapply typed_structure_planned_member; eauto. }
  pose proof (program_composites_consistent p sid co Hco) as Hconsistent.
  destruct (program_composite_shape p sid co Hco) as [Hstruct Hplain].
  assert (Hbounds : forall f, In f fs -> 0 <= planned_offset f /\
    planned_offset f + sizeof_ptype (planned_type f) <= co.(co_sizeof)).
  { intros f Hin.
    pose proof (Ctypes.field_offset_in_range _ _ _ _ _ (Hoffsets f Hin)
      (source_member_type_translation _ _ _ (Htypes f Hin))) as [Hlo Hhi].
    pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as Hbound.
    pose proof (primitive_chunk_size_translation (bcomposite_composite_env p.(prog_comp_env))
      (planned_type f)) as Hwidth.
    rewrite primitive_chunk_size in Hwidth. split; [exact Hlo|lia]. }
  assert (Hrepresentable : forall f, In f fs -> 0 <= planned_offset f <= Ptrofs.max_unsigned).
  { intros f Hin. specialize (Hbounds f Hin). pose proof (primitive_size_positive (planned_type f)); lia. }
  eapply fresh_declared_initializer_coherence; [exact Hobjects|exact Hmemory|exact Hcoherent|exact Ha| |].
  - intros cell_delta ty chunk Hleaf child_delta child Hpath.
    exact (program_scalar_leaf_subobject p _ _ _ _ _ _ Hleaf Hpath).
  - intros b ofs ty chunk Hcell.
    destruct (extend_field_layout_origin _ _ _ _ _ _ _ _ Hcell)
      as [Hold|[f [Hin [Hb [Hofs [Hty Hchunk]]]]]]; [left; exact Hold|].
    subst b ofs ty chunk. right; split; [reflexivity|].
    change (scalar_object_leaf (prog_comp_env p) (Stype sid attr) (planned_start Ptrofs.zero f)
      (Vtype (planned_type f)) (planned_chunk f)).
    rewrite initializer_planned_start by (apply Hrepresentable; exact Hin).
    split; [|apply primitive_chunk_access].
    replace (planned_offset f) with (0 + planned_offset f) at 1 by lia.
    eapply path_field with (co := co) (field := planned_field f).
    + apply path_root. simpl. rewrite Hco. pose proof (co_sizeof_pos co); lia.
    + exact Hco.
    + unfold Ctyping.type_of_member. rewrite (source_member_type_translation _ _ _ (Htypes f Hin)). reflexivity.
    + exact (Htypes f Hin).
    + exact (Hoffsets f Hin).
    + exact (proj1 (Hbounds f Hin)).
    + simpl. pose proof (primitive_size_positive (planned_type f)); lia.
    + simpl. rewrite Hco. exact (proj2 (Hbounds f Hin)).
Qed.

Print Assumptions program_primitive_structure_initializer_coherence.
