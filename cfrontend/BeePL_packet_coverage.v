(* Every embedded Bytes leaf is registered as a packet descriptor. Paths do
   not follow pointer values; standalone descriptors retain their separate
   packet_state_typed obligation. No scalar-cell fiction is used for Bytes. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_memory BeePL_object_paths BeePL_object_coverage BeePL_fresh_copy.
Require Import BeePL_packet BeePL_packet_descriptor_copy BeePL_packet_state BeePL_bytes_execution.
Require Import BeePL_soundness_arrays BeePL_soundness_memory.
Import ListNotations.
Local Open Scope Z_scope.

Definition bytes_object_leaf (cenv : bcomposite_env) (root : type) (delta : Z) : Prop :=
  object_path cenv root delta Bytes.

Lemma unit_has_no_bytes_leaf : forall cenv delta,
  ~ bytes_object_leaf cenv Utype delta.
Proof.
  intros cenv delta Hpath.
  destruct (object_path_bounds _ _ _ _ Hpath) as [Hdelta [Hsize Hbound]].
  change (delta + packet_descriptor_size <= 0) in Hbound.
  pose proof packet_descriptor_size_positive; lia.
Qed.

Definition packet_object_coverage (cenv : bcomposite_env)
    (objects : aggregate_object_context) (locations : packet_locations) : Prop :=
  forall block base root, objects block base root -> forall delta,
    bytes_object_leaf cenv root delta ->
    locations block (Ptrofs.repr (Ptrofs.unsigned base + delta)).

Lemma packet_coverage_locations_extension : forall cenv objects locations larger,
  packet_object_coverage cenv objects locations ->
  (forall block offset, locations block offset -> larger block offset) ->
  packet_object_coverage cenv objects larger.
Proof. unfold packet_object_coverage; eauto. Qed.

Lemma covered_bytes_offset_bounds : forall cenv Sigma m objects block base root delta,
  aggregate_objects_valid cenv Sigma m objects -> objects block base root ->
  bytes_object_leaf cenv root delta ->
  0 <= delta <= Ptrofs.max_unsigned /\
  Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned base + delta)) = Ptrofs.unsigned base + delta /\
  Ptrofs.unsigned base + delta + packet_descriptor_size <= Ptrofs.modulus.
Proof.
  intros cenv Sigma m objects block base root delta Hvalid Hobject Hleaf.
  pose proof (object_path_bounds _ _ _ _ Hleaf) as [Hdelta [Hsize Hinside]].
  destruct (aggregate_object_readable _ _ _ _ Hvalid _ _ _ Hobject)
    as [_ [_ [Hbound Hrest]]].
  change (delta + packet_descriptor_size <= sizeof_type cenv root) in Hinside.
  pose proof packet_descriptor_size_positive.
  pose proof (Ptrofs.unsigned_range base).
  split; [unfold Ptrofs.max_unsigned; lia|]. split; [|lia].
  apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned; lia.
Qed.

Lemma covered_bytes_address_add : forall cenv Sigma m objects block base root delta,
  aggregate_objects_valid cenv Sigma m objects -> objects block base root ->
  bytes_object_leaf cenv root delta ->
  Ptrofs.add base (Ptrofs.repr delta) = Ptrofs.repr (Ptrofs.unsigned base + delta).
Proof.
  intros. destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ H H0 H1) as [Hdelta _].
  unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr by exact Hdelta. reflexivity.
Qed.

Theorem covered_packet_leaf_read : forall cenv Gamma Sigma m objects locations block base root delta,
  aggregate_objects_valid cenv Sigma m objects -> objects block base root ->
  packet_object_coverage cenv objects locations -> packet_state_valid m locations ->
  bytes_object_leaf cenv root delta ->
  let address := Ptrofs.repr (Ptrofs.unsigned base + delta) in
  locations block address /\
  object_type_at cenv Sigma block (Ptrofs.unsigned address) Bytes /\
  type_expr cenv Gamma Sigma (Val (Vloc block address) Bytes) [] Bytes /\
  deref_addr Bytes m block address Full (Vloc block address).
Proof.
  intros cenv Gamma Sigma m objects locations block base root delta Hobjects Hobject Hcoverage Hpackets Hleaf address.
  pose proof (Hcoverage _ _ _ Hobject _ Hleaf) as Hentry.
  destruct (covered_bytes_offset_bounds _ _ _ _ _ _ _ _ Hobjects Hobject Hleaf)
    as [Hdelta [Hoffset Hbound]].
  assert (Htyped : object_type_at cenv Sigma block (Ptrofs.unsigned address) Bytes).
  { unfold address. rewrite Hoffset. eapply object_path_typing; [exact Hleaf|].
    eapply aggregate_object_typing; eauto. }
  split; [exact Hentry|]. split; [exact Htyped|]. split; [constructor; exact Htyped|].
  destruct (Hpackets _ _ Hentry) as [Hextent [view [bytes [Hdescriptor Hdata]]]].
  eapply bytes_descriptor_read; eauto.
Qed.

Theorem packet_coverage_subobject_extension : forall cenv objects locations block base root delta child result,
  packet_object_coverage cenv objects locations -> objects block base root ->
  object_path cenv root delta child ->
  Ptrofs.unsigned result = Ptrofs.unsigned base + delta ->
  packet_object_coverage cenv (add_aggregate_descriptor objects block result child) locations.
Proof.
  intros cenv objects locations block base root delta child result Hcoverage Hobject Hpath Hresult
    b offset ty [Hold|[Hb [Hoffset Hty]]] leafDelta Hleaf.
  - eapply Hcoverage; eauto.
  - subst b offset ty. unfold bytes_object_leaf in *.
    pose proof (object_path_compose _ _ _ _ _ _ Hpath Hleaf) as Hcombined.
    pose proof (Hcoverage _ _ _ Hobject _ Hcombined) as Hentry.
    rewrite Hresult. replace (Ptrofs.unsigned base + delta + leafDelta)
      with (Ptrofs.unsigned base + (delta + leafDelta)) by lia. exact Hentry.
Qed.

Lemma bytes_array_leaf : forall cenv len attr index,
  (index < Z.to_nat len)%nat ->
  bytes_object_leaf cenv (Atype Bytes len attr) (Z.of_nat index * sizeof_type cenv Bytes).
Proof.
  intros cenv len attr index Hindex.
  assert (Hlen : 0 <= len) by (destruct len; simpl in Hindex; lia).
  assert (Hbounds : 0 <= Z.of_nat index < len).
  { split; [lia|]. apply Nat2Z.inj_lt in Hindex. rewrite Z2Nat.id in Hindex by lia. lia. }
  unfold bytes_object_leaf. replace (Z.of_nat index * sizeof_type cenv Bytes)
    with (0 + Z.of_nat index * sizeof_type cenv Bytes) by lia.
  eapply path_array_element.
  - constructor. change (0 <= packet_descriptor_size * Z.max 0 len).
    rewrite Z.max_r by lia. pose proof packet_descriptor_size_positive; nia.
  - exact Hbounds.
  - change (0 <= packet_descriptor_size). pose proof packet_descriptor_size_positive; lia.
Qed.

Theorem covered_bytes_array_read_progress :
  forall ge Gamma Sigma m objects locations block base len attr index p vm ef,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects block base (Atype Bytes len attr) ->
  packet_object_coverage ge.(genv_cenv) objects locations -> packet_state_valid m locations ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead index) [Val (Vloc block base) (Atype Bytes len attr)] Bytes) ef Bytes ->
  let address := Ptrofs.add base (Ptrofs.repr (Z.of_nat index * sizeof_type ge.(genv_cenv) Bytes)) in
  locations block address /\
  ssem_expr ge p vm m (Prim (ArrayRead index) [Val (Vloc block base) (Atype Bytes len attr)] Bytes)
    m vm (Val (Vloc block address) Bytes) /\
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc block address) Bytes) [] Bytes.
Proof.
  intros ge Gamma Sigma m objects locations block base len attr index p vm ef
    Hobjects Hobject Hcoverage Hpackets Htyped address.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hindex].
  pose proof (bytes_array_leaf ge.(genv_cenv) len attr index Hindex) as Hleaf.
  destruct (covered_packet_leaf_read _ Gamma _ _ _ _ _ _ _ _ Hobjects Hobject Hcoverage Hpackets Hleaf)
    as [Hentry [Hidentity [Hvalue Hread]]].
  assert (Haddress : address = Ptrofs.repr (Ptrofs.unsigned base + Z.of_nat index * sizeof_type ge.(genv_cenv) Bytes)).
  { unfold address. eapply covered_bytes_address_add; eauto. }
  rewrite <- Haddress in Hentry, Hidentity, Hvalue, Hread.
  split; [exact Hentry|]. split; [|exact Hvalue].
  eapply ssem_array_read_value; eauto.
Qed.

Theorem covered_bytes_field_read_progress :
  forall ge Gamma Sigma m objects locations block base sid attr co field delta receiver p vm,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects -> objects block base (Stype sid attr) ->
  packet_object_coverage ge.(genv_cenv) objects locations -> packet_state_valid m locations ->
  (receiver = Stype sid attr \/ receiver = Ptrtype (Reftype (Bstruct sid attr) noattr)) ->
  PTree.get sid ge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env ge.(genv_cenv)) field (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  bytes_object_leaf ge.(genv_cenv) (Stype sid attr) delta ->
  let address := Ptrofs.add base (Ptrofs.repr delta) in
  locations block address /\
  ssem_expr ge p vm m (Sfield (Val (Vloc block base) receiver) field Bytes)
    m vm (Val (Vloc block address) Bytes) /\
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc block address) Bytes) [] Bytes.
Proof.
  intros ge Gamma Sigma m objects locations block base sid attr co field delta receiver p vm
    Hobjects Hobject Hcoverage Hpackets Hreceiver Hco Hoffset Hleaf address.
  destruct (covered_packet_leaf_read _ Gamma _ _ _ _ _ _ _ _ Hobjects Hobject Hcoverage Hpackets Hleaf)
    as [Hentry [Hidentity [Hvalue Hread]]].
  assert (Haddress : address = Ptrofs.repr (Ptrofs.unsigned base + delta)).
  { unfold address. eapply covered_bytes_address_add; eauto. }
  rewrite <- Haddress in Hentry, Hidentity, Hvalue, Hread.
  split; [exact Hentry|]. split; [|exact Hvalue].
  destruct Hreceiver; subst receiver; [eapply ssem_sfield_struct|eapply ssem_sfield2]; eauto.
Qed.

Print Assumptions covered_packet_leaf_read.
Print Assumptions packet_coverage_subobject_extension.
Print Assumptions covered_bytes_array_read_progress.
Print Assumptions covered_bytes_field_read_progress.

Theorem covered_bytes_array_read_preservation :
  forall ge Gamma Sigma m objects locations block base len attr index p vm ef final vm' next,
  aggregate_objects_valid ge.(genv_cenv) Sigma m objects ->
  objects block base (Atype Bytes len attr) ->
  packet_object_coverage ge.(genv_cenv) objects locations -> packet_state_valid m locations ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead index) [Val (Vloc block base) (Atype Bytes len attr)] Bytes) ef Bytes ->
  ssem_expr ge p vm m (Prim (ArrayRead index) [Val (Vloc block base) (Atype Bytes len attr)] Bytes)
    final vm' next ->
  final = m /\ vm' = vm /\
  exists address, next = Val (Vloc block address) Bytes /\ locations block address /\
    type_expr ge.(genv_cenv) Gamma Sigma next [] Bytes.
Proof.
  intros ge Gamma Sigma m objects locations block base len attr index p vm ef final vm' next
    Hobjects Hobject Hcoverage Hpackets Htyped Hstep.
  destruct (covered_bytes_array_read_progress ge Gamma Sigma m objects locations block base len attr
    index p vm ef Hobjects Hobject Hcoverage Hpackets Htyped) as [Hentry [Hexpected Hvalue]].
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with Hread : aggregate_readable _ _ _ _ Bytes |- _ =>
      destruct Hread as [Hkind _]; discriminate end].
  match goal with Hread : deref_addr Bytes _ _ _ Full _ |- _ =>
    pose proof (bytes_read_exact _ _ _ _ Hread) as Hresult; subst end.
  split; [reflexivity|]. split; [reflexivity|]. eexists. split; [reflexivity|]. split; assumption.
Qed.

Print Assumptions covered_bytes_array_read_preservation.
