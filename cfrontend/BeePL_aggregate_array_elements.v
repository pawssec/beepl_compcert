(* Embedded aggregate array elements are descriptors of subobjects. Their
   initialized scalar leaves come from parent coverage, not a scalar read of
   the whole aggregate. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_object_coverage.
Require Import BeePL_aggregate_dereference.
Local Open Scope Z_scope.

Lemma aggregate_array_element_path : forall cenv Sigma m objects b base elem len attr n,
  aggregate_objects_valid cenv Sigma m objects ->
  objects b base (Atype elem len attr) ->
  (n < Z.to_nat len)%nat ->
  object_path cenv (Atype elem len attr) (Z.of_nat n * sizeof_type cenv elem) elem /\
  0 <= Ptrofs.unsigned base + Z.of_nat n * sizeof_type cenv elem <= Ptrofs.max_unsigned /\
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type cenv elem))) =
    Ptrofs.unsigned base + Z.of_nat n * sizeof_type cenv elem.
Proof.
  intros cenv Sigma m objects b base elem len attr n Hobjects Hsource Hindex.
  assert (Hlen : 0 <= len).
  { destruct len; simpl in Hindex; lia. }
  assert (HindexZ : 0 <= Z.of_nat n < len).
  { rewrite <- (Z2Nat.id len Hlen). split; [lia |]. apply Nat2Z.inj_lt; exact Hindex. }
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hsource)
    as [Hkind [HparentSize [Hextent Hrest]]].
  assert (Hsize : 0 <= sizeof_type cenv elem).
  { simpl in HparentSize. rewrite Z.max_r in HparentSize by lia. nia. }
  assert (Hpath : object_path cenv (Atype elem len attr)
      (Z.of_nat n * sizeof_type cenv elem) elem).
  { replace (Z.of_nat n * sizeof_type cenv elem)
      with (0 + Z.of_nat n * sizeof_type cenv elem) by lia.
    eapply path_array_element; [apply path_root; exact HparentSize | exact HindexZ | exact Hsize]. }
  pose proof (Ptrofs.unsigned_range base) as Hbase.
  assert (Hraw : 0 <= Ptrofs.unsigned base + Z.of_nat n * sizeof_type cenv elem <= Ptrofs.max_unsigned).
  { simpl in Hextent. rewrite Z.max_r in Hextent by lia.
    unfold Ptrofs.max_unsigned. destruct (Z.eq_dec (sizeof_type cenv elem) 0); nia. }
  split; [exact Hpath |]. split; [exact Hraw |].
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr (Z.of_nat n * sizeof_type cenv elem))
    by (unfold Ptrofs.max_unsigned in *; nia).
  apply Ptrofs.unsigned_repr; exact Hraw.
Qed.

Theorem initialized_aggregate_array_element :
  forall ge Sigma Gamma m objects cells b base elem len attr n,
  initialized_object_memory ge Sigma m objects cells ->
  objects b base (Atype elem len attr) ->
  (n < Z.to_nat len)%nat ->
  is_aggregate_type elem = true ->
  let delta := Z.of_nat n * sizeof_type ge.(genv_cenv) elem in
  let result := Ptrofs.add base (Ptrofs.repr delta) in
  let objects' := add_aggregate_descriptor objects b result elem in
  0 <= Ptrofs.unsigned base + delta <= Ptrofs.max_unsigned /\
  object_path ge.(genv_cenv) (Atype elem len attr) delta elem /\
  Ptrofs.unsigned result = Ptrofs.unsigned base + delta /\
  initialized_object_memory ge Sigma m objects' cells /\
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc b result) elem) nil elem /\
  runtime_locations (descriptor_heap_locations ge cells objects') (Val (Vloc b result) elem) /\
  aggregate_readable ge.(genv_cenv) m b result elem.
Proof.
  intros ge Sigma Gamma m objects cells b base elem len attr n Hinitial Hsource Hindex Hkind.
  cbn zeta.
  pose proof (initialized_object_descriptors _ _ _ _ _ Hinitial) as Hobjects.
  destruct (aggregate_array_element_path _ _ _ _ _ _ _ _ _ _ Hobjects Hsource Hindex)
    as [Hpath [Hraw Hresult]].
  pose proof (initialized_object_subobject_extension ge Sigma m objects cells b base
    (Atype elem len attr) (Z.of_nat n * sizeof_type ge.(genv_cenv) elem) elem
    (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)))
    Hinitial Hsource Hpath Hkind Hresult) as Hnew.
  pose proof (initialized_object_descriptors _ _ _ _ _ Hnew) as HnewObjects.
  assert (Hchild : add_aggregate_descriptor objects b
    (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem b
    (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem).
  { right; auto. }
  split; [exact Hraw |]. split; [exact Hpath |]. split; [exact Hresult |].
  split; [exact Hnew |]. split.
  - eapply aggregate_descriptor_value_typed; eauto.
  - split.
    + apply aggregate_descriptor_direct; assumption.
    + eapply aggregate_object_readable; eauto.
Qed.

Print Assumptions aggregate_array_element_path.
Print Assumptions initialized_aggregate_array_element.
