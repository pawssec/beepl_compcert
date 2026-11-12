(* Scalar reads obtained from initialized aggregate coverage, rather than a
   separately assumed cell for the particular source operation. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_soundness_arrays BeePL_soundness_fields BeePL_aggregate_memory.
Require Import BeePL_object_paths BeePL_object_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Lemma covered_leaf_cell_add : forall ge Sigma m objects cells b base root delta ty chunk,
  initialized_object_memory ge Sigma m objects cells -> objects b base root ->
  scalar_object_leaf ge.(genv_cenv) root delta ty chunk ->
  exists stored_chunk, cells b (Ptrofs.add base (Ptrofs.repr delta)) ty stored_chunk /\
    transl_bchunk_cchunk stored_chunk = transl_bchunk_cchunk chunk.
Proof.
  intros ge Sigma m objects cells b base root delta ty chunk Hmemory Hobject Hleaf.
  destruct Hmemory as [Hobjects Hcoverage Htyped Hlocations HscalarCoherence].
  pose proof (Hcoverage _ _ _ Hobject _ _ _ Hleaf) as Hcell.
  pose proof (scalar_object_leaf_bounds _ _ _ _ _ Hleaf) as Hbounds.
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [Hkind [Hsize [Hextent Hrest]]].
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)).
  pose proof (Ptrofs.unsigned_range base).
  unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr; [exact Hcell |].
  unfold Ptrofs.max_unsigned. lia.
Qed.

Lemma covered_array_leaf : forall ge Sigma m objects cells b base elem len attr n chunk,
  initialized_object_memory ge Sigma m objects cells ->
  objects b base (Atype elem len attr) ->
  (n < Z.to_nat len)%nat ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  scalar_object_leaf ge.(genv_cenv) (Atype elem len attr)
    (Z.of_nat n * sizeof_type ge.(genv_cenv) elem) elem chunk.
Proof.
  intros ge Sigma m objects cells b base elem len attr n chunk Hmemory Hobject Hbound Hmode.
  destruct Hmemory as [Hobjects Hcoverage Htyped Hlocations HscalarCoherence].
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [Hkind [Hsize Hrest]].
  assert (Hindex : 0 <= Z.of_nat n < len).
  { split; [lia |]. apply Nat2Z.inj_lt in Hbound. rewrite Z2Nat.id in Hbound by lia. lia. }
  split; [|exact Hmode].
  replace (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)
    with (0 + Z.of_nat n * sizeof_type ge.(genv_cenv) elem) by lia.
  eapply path_array_element; [constructor; exact Hsize |exact Hindex|].
  rewrite <- (scalar_type_chunk_size ge.(genv_cenv) elem _ Hmode).
  pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)). lia.
Qed.

Theorem covered_array_read_progress :
  forall ge Gamma Sigma objects cells p vm m b base elem len attr n ef chunk,
  initialized_object_memory ge Sigma m objects cells -> objects b base (Atype elem len attr) ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  exists v, ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) m vm (Val v elem) /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val v elem) ef elem /\
    runtime_locations (descriptor_heap_locations ge cells objects) (Val v elem).
Proof.
  intros ge Gamma Sigma objects cells p vm m b base elem len attr n ef chunk Hmemory Hobject Hmode Htyped.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hbound]. subst ef.
  pose proof (covered_array_leaf _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hbound Hmode) as Hleaf.
  destruct (covered_leaf_cell_add _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hleaf)
    as [stored [Hcell Hchunk]].
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocations HscalarCoherence].
  destruct (typed_memory_cell_read _ Gamma _ _ _ _ _ _ (Hcells _ _ _ _ Hcell)) as [v [Hread Hvalue]].
  exists v. split; [eapply ssem_array_read_value; eauto |]. split; [exact Hvalue |].
  simpl. eapply Hlocations; eauto.
Qed.

Theorem covered_array_read_preservation :
  forall ge Gamma Sigma objects cells p vm m b base elem len attr n ef chunk m' vm' e',
  initialized_object_memory ge Sigma m objects cells -> objects b base (Atype elem len attr) ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr ge.(genv_cenv) Gamma Sigma e' ef elem /\
    runtime_locations (descriptor_heap_locations ge cells objects) e'.
Proof.
  intros ge Gamma Sigma objects cells p vm m b base elem len attr n ef chunk m' vm' e'
    Hmemory Hobject Hmode Htyped Hstep.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hbound]. subst ef.
  pose proof (covered_array_leaf _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hbound Hmode) as Hleaf.
  destruct (covered_leaf_cell_add _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hleaf)
    as [stored [Hcell Hchunk]].
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocations HscalarCoherence].
  assert (Hscalar : is_aggregate_type elem = false) by (eapply by_value_type_not_aggregate; exact Hmode).
  inversion Hstep; subst; try discriminate Hmode; try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with H : aggregate_readable _ _ _ _ _ |- _ => destruct H as [Hkind _] end; congruence].
  repeat split; try reflexivity.
  - eapply typed_memory_cell_read_preservation; [apply Hcells; exact Hcell | eassumption].
  - eapply Hlocations; eauto.
Qed.

Theorem covered_field_read_progress :
  forall ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk,
  initialized_object_memory ge Sigma m objects cells -> objects b base (Stype sid attr) ->
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env ge.(genv_cenv)) field
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  object_path ge.(genv_cenv) (Stype sid attr) delta ty ->
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  exists v, ssem_expr ge p vm m (Sfield (Val (Vloc b base) receiver) field ty)
    m vm (Val v ty) /\ type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations (descriptor_heap_locations ge cells objects) (Val v ty).
Proof.
  intros ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk
    Hmemory Hobject Hreceiver Hco Hoffset Hpath Hmode.
  assert (Hleaf : scalar_object_leaf ge.(genv_cenv) (Stype sid attr) delta ty chunk) by (split; assumption).
  destruct (covered_leaf_cell_add _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hleaf)
    as [stored [Hcell Hchunk]].
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocations HscalarCoherence].
  destruct (typed_memory_cell_read _ Gamma _ _ _ _ _ _ (Hcells _ _ _ _ Hcell)) as [v [Hread Hvalue]].
  exists v. split.
  - destruct Hreceiver; subst receiver; [eapply ssem_sfield_struct | eapply ssem_sfield2]; eauto.
  - split; [exact Hvalue |]. simpl. eapply Hlocations; eauto.
Qed.

Theorem covered_field_read_preservation :
  forall ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk m' vm' e',
  initialized_object_memory ge Sigma m objects cells -> objects b base (Stype sid attr) ->
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env ge.(genv_cenv)) field
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  object_path ge.(genv_cenv) (Stype sid attr) delta ty ->
  access_mode_type ty = By_value (transl_bchunk_cchunk chunk) ->
  ssem_expr ge p vm m (Sfield (Val (Vloc b base) receiver) field ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr ge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations (descriptor_heap_locations ge cells objects) e'.
Proof.
  intros ge Gamma Sigma objects cells p vm m b base sid attr receiver field ty co delta chunk m' vm' e'
    Hmemory Hobject Hreceiver Hco Hoffset Hpath Hmode Hstep.
  assert (Hleaf : scalar_object_leaf ge.(genv_cenv) (Stype sid attr) delta ty chunk) by (split; assumption).
  destruct (covered_leaf_cell_add _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hleaf)
    as [stored [Hcell Hchunk]].
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocations HscalarCoherence].
  assert (Hscalar : (is_aggregate_type ty || is_bytes ty)%bool = false).
  { eapply typed_cell_not_aggregate. apply Hcells. exact Hcell. }
  destruct Hreceiver; subst receiver; inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with H : aggregate_field_access _ _ _ _ _ _ _ _ |- _ => inversion H; subst end; congruence].
  all: assert (co0 = co) by congruence; subst co0.
  all: assert (delta0 = delta /\ bf = Full) by (split; congruence).
  all: destruct H as [Hd Hbf]; subst delta0 bf.
  all: repeat split; try reflexivity.
  all: try solve [eapply typed_memory_cell_read_preservation; [apply Hcells; exact Hcell | eassumption]].
  all: eapply Hlocations; eauto.
Qed.

Print Assumptions covered_array_read_progress.
Print Assumptions covered_array_read_preservation.
Print Assumptions covered_field_read_progress.
Print Assumptions covered_field_read_preservation.
