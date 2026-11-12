(* Regression witnesses for incorrect assumptions in the unfinished proofs.
   These proofs intentionally import definitions, not the admitted operator or
   type-soundness theorems. They must remain free of project axioms. *)
Require Import ZArith Lia Integers AST Maps Memory Ctypes BeeTypes BeePL_values.
Require Import BeePL BeePL_packet BeePL_sem BeePL_typesystem.
Require Import List Globalenvs.
Import ListNotations.

Local Open Scope Z_scope.

(* ty_vali currently permits every Int.int at every integer width/signedness.
   This refutes the former int_range_invalid axiom, which has been removed. *)
Lemma unsigned_min_signed_counterexample : forall cenv Gamma Sigma sz a,
  type_expr cenv Gamma Sigma
    (Val (Vint (Int.repr Int.min_signed)) (Vtype (Tint sz Unsigned a)))
    nil (Vtype (Tint sz Unsigned a)) /\
  negb (Int.eq (Int.repr Int.min_signed) (Int.repr Int.min_signed)) = false.
Proof.
  intros. split.
  - apply ty_vali.
  - rewrite Int.eq_true. reflexivity.
Qed.

(* The present location invariant asks for a whole scalar load at every byte
   offset from zero through the chunk size. Offset 1 is unaligned for Mint32,
   so no store with an int32 entry can satisfy this invariant. *)
Lemma int32_location_invariant_counterexample : forall Sigma m b a,
  PTree.get b Sigma = Some (Vtype (Tint I32 Signed a)) ->
  ~ well_formed_loc Sigma m.
Proof.
  intros Sigma m b a Hentry Hloc.
  inversion Hloc as [Haccess].
  assert (Hrange : 0 <= 1 <= size_chunk (transl_bchunk_cchunk BMint32)) by
    (simpl; lia).
  specialize (Haccess b 1 (Vtype (Tint I32 Signed a)) BMint32 Hentry eq_refl Hrange).
  destruct Haccess as [_ Halign].
  simpl in Halign. destruct Halign as [k Hk]. lia.
Qed.

Print Assumptions unsigned_min_signed_counterexample.
Print Assumptions int32_location_invariant_counterexample.

(* A successful CompCert load does not imply initialization. Freshly allocated
   readable memory loads Vundef, which BeePL explicitly refuses to convert. *)
Lemma fresh_allocation_undefined_counterexample : forall m m' b,
  Mem.alloc m 0 4 = (m', b) ->
  Mem.load Mint32 m' b 0 = Some Values.Vundef /\
  exists error, trans_cvalue_bvalue Values.Vundef = Errors.Error error.
Proof.
  intros m m' b Halloc. split.
  - eapply Mem.load_alloc_same'; eauto; simpl; try lia.
    exists 0. reflexivity.
  - eexists. reflexivity.
Qed.

Print Assumptions fresh_allocation_undefined_counterexample.

(* Block membership alone cannot type a reference at an arbitrary byte offset.
   An int32 reference at offset one is accepted, but every full int32 read there
   fails CompCert's alignment requirement, regardless of the memory contents. *)
Lemma unaligned_int32_reference_typed : forall cenv Gamma Sigma b,
  PTree.get b Sigma = Some (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)) ->
  type_expr cenv Gamma Sigma
    (Prim Deref
      (Val (Vloc b (Ptrofs.repr 1))
        (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)) :: nil)
      (Vtype (Tint I32 Signed noattr)))
    (Read :: nil) (Vtype (Tint I32 Signed noattr)).
Proof.
  intros cenv Gamma Sigma b Hentry.
  change (Read :: nil) with (nil ++ (Read :: nil))%list.
  apply ty_deref with (pt := Reftype (Bprim (Tint I32 Signed noattr)) noattr)
    (ef := nil); [apply ty_valloc; exact Hentry | reflexivity | reflexivity].
Qed.

Lemma unaligned_int32_read_impossible : forall m b v,
  ~ deref_addr (Vtype (Tint I32 Signed noattr)) m b (Ptrofs.repr 1) Full v.
Proof.
  intros m b v Hread. inversion Hread; subst; try discriminate.
  match goal with Hmode : access_mode_type _ = _ |- _ =>
    simpl in Hmode; inversion Hmode
  end.
  match goal with Hload : Mem.loadv _ _ _ = Some _ |- _ =>
    simpl in Hload; apply Mem.load_valid_access in Hload;
    destruct Hload as [_ Halign]
  end.
  assert (Hone : Ptrofs.unsigned (Ptrofs.repr 1) = 1) by reflexivity.
  rewrite Hone in Halign. simpl in Halign.
  match goal with Hchunk : Mint32 = transl_bchunk_cchunk _ |- _ =>
    rewrite <- Hchunk in Halign
  end. simpl in Halign.
  destruct Halign as [k Hk]. lia.
Qed.

Lemma unaligned_int32_reference_stuck : forall bge p vm m b m' vm' e',
  ~ ssem_expr bge p vm m
    (Prim Deref
      (Val (Vloc b (Ptrofs.repr 1))
        (Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr)) :: nil)
      (Vtype (Tint I32 Signed noattr))) m' vm' e'.
Proof.
  intros bge p vm m b m' vm' e' Hstep. inversion Hstep; subst.
  - match goal with Hvalue : ssem_expr _ _ _ _ (Val _ _) _ _ _ |- _ => inversion Hvalue end.
  - eapply unaligned_int32_read_impossible; eauto.
  - match goal with H : aggregate_readable _ _ _ _ _ |- _ =>
      destruct H as [Hkind _]; discriminate Hkind end.
Qed.

Print Assumptions unaligned_int32_reference_typed.
Print Assumptions unaligned_int32_reference_stuck.

(* The raw single-definition builder accepts an intrinsic Bytes member even when the
   translated environment has no bytes_t definition. This is a real missing
   premise in a blanket composite-consistency theorem, not a tactic failure.
   The public program builder now seeds bytes_t first; the counterexample
   remains a regression witness for bypassing that initialization. *)
Lemma bytes_member_completeness_mismatch :
  bcomplete_members (PTree.empty bcomposite)
    [BeeTypes.Member_plain 1%positive Bytes] = true /\
  Ctypes.complete_members (bcomposite_composite_env (PTree.empty bcomposite))
    (bmembers_cmembers [BeeTypes.Member_plain 1%positive Bytes]) = false.
Proof. split; reflexivity. Qed.

Lemma bytes_composite_consistency_counterexample : exists co,
  bcomposite_of_def (PTree.empty bcomposite) 2%positive Struct
    [BeeTypes.Member_plain 1%positive Bytes] noattr = Errors.OK co /\
  ~ Ctypes.composite_consistent
      (bcomposite_composite_env (PTree.empty bcomposite)) (bcomposite_ccomposite co).
Proof.
  eexists. split; [reflexivity |].
  intro H. pose proof (Ctypes.co_consistent_complete _ _ H) as Hcomplete.
  discriminate Hcomplete.
Qed.

Print Assumptions bytes_composite_consistency_counterexample.

(* Named reads must have a matching static binding. *)
Lemma unbound_array_access_rejected : forall cenv Gamma Sigma arr ty index result ef,
  PTree.get arr Gamma = None ->
  ~ type_expr cenv Gamma Sigma (Aaccess arr ty index result) ef result.
Proof. intros cenv Gamma Sigma arr ty index result ef Hnone Htyped.
  inversion Htyped; subst; congruence.
Qed.

Lemma unbound_array_access_stuck : forall (bge : BeePL.genv) p vm m arr ty index result,
  PTree.get arr vm = None -> Globalenvs.Genv.find_symbol bge arr = None ->
  forall m' vm' e', ~ ssem_expr bge p vm m (Aaccess arr ty index result) m' vm' e'.
Proof.
  intros bge p vm m arr ty index result Hmissing Hglobal m' vm' e' Hstep.
  inversion Hstep; subst;
    try solve [change (@PTree.get (Values.block * type) arr vm' = None) in Hmissing;
      match goal with H : PTree.get arr vm' = Some _ |- _ =>
        rewrite Hmissing in H; discriminate end];
    match goal with H : Globalenvs.Genv.find_symbol _ arr = Some _ |- _ =>
      rewrite Hglobal in H; discriminate end.
Qed.

Print Assumptions unbound_array_access_rejected.
Print Assumptions unbound_array_access_stuck.

(* Regression for integer promotion: the uint8 overflow shape formerly got
   stuck because its unsigned guard disagreed with C's signed-int32 operation. *)
Lemma narrow_unsigned_division_guarded : forall bge p vm m,
  let ty := Vtype (Tint I8 Unsigned noattr) in
  ssem_expr bge p vm m
    (Prim (Bop Cop.Odiv)
      [Val (Vint (Int.repr Int.min_signed)) ty; Val (Vint Int.mone) ty] ty)
    m vm (Val (Vint Int.zero) ty).
Proof.
  intros bge p vm m ty. subst ty.
  eapply ssem_bop3_unsafe with (s := Signed); reflexivity.
Qed.

Print Assumptions narrow_unsigned_division_guarded.

(* Regression for the frontend's header/fallback shape. *)
Lemma bytes_two_branch_pattern_accepted : forall header schema fields rest,
  valid_match_patterns Bytes
    [Pbytes header (Stype schema noattr) fields; Pbytes rest Bytes nil].
Proof. intros; do 4 eexists; reflexivity. Qed.

Lemma bytes_single_branch_pattern_rejected : forall header schema fields,
  ~ valid_match_patterns Bytes [Pbytes header schema fields].
Proof.
  intros header schema fields [x [s [fs [rest Hshape]]]]. discriminate.
Qed.

(* The earlier typed binder-escape witness is now excluded by the pattern
   shape rule. This does not repair the execution rule for valid Bytes matches. *)
Lemma bytes_single_branch_match_untypable :
  forall cenv Gamma Sigma scrutinee header schema fields body rt ef,
  typeof_expr scrutinee = Bytes ->
  ~ type_expr cenv Gamma Sigma
      (Match scrutinee [Pbytes header schema fields] [body] rt) ef rt.
Proof.
  intros cenv Gamma Sigma scrutinee header schema fields body rt ef Hbytes Htyped.
  destruct (type_infer_match _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [efe [te [efb [effects [Heffect [Hscrut [Hpatterns Hremaining]]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hscrut) as Htype.
  rewrite Hbytes in Htype. subst te.
  eapply bytes_single_branch_pattern_rejected; exact Hpatterns.
Qed.

Lemma bytes_two_branch_match_typable :
  forall cenv Gamma Sigma scrutinee header schema fields rest yes no rt ef,
  packet_schema_valid cenv schema fields ->
  type_expr cenv Gamma Sigma scrutinee ef Bytes ->
  type_expr cenv (pattern_context Gamma (Pbytes header (Stype schema noattr) fields) Bytes)
    Sigma yes nil rt ->
  type_expr cenv (pattern_context Gamma (Pbytes rest Bytes nil) Bytes)
    Sigma no nil rt ->
  type_expr cenv Gamma Sigma
    (Match scrutinee [Pbytes header (Stype schema noattr) fields; Pbytes rest Bytes nil]
      [yes; no] rt) (ef ++ nil) rt.
Proof.
  intros cenv Gamma Sigma scrutinee header schema fields rest yes no rt ef Hschema Hscrut Hyes Hno.
  eapply ty_matcho with (te := Bytes) (branch_effect := fun _ => nil).
  - exact Hscrut.
  - apply bytes_two_branch_pattern_accepted.
  - constructor; [exact Hschema |]. constructor; [exact I | constructor].
  - reflexivity.
  - intros n pat branch Hpat Hbranch.
    destruct n as [|[|n]].
    + simpl in Hpat, Hbranch. inversion Hpat; inversion Hbranch; subst. exact Hyes.
    + simpl in Hpat, Hbranch. inversion Hpat; inversion Hbranch; subst. exact Hno.
    + destruct n; discriminate.
  - intros. reflexivity.
Qed.

Print Assumptions bytes_two_branch_pattern_accepted.
Print Assumptions bytes_single_branch_pattern_rejected.
Print Assumptions bytes_single_branch_match_untypable.
Print Assumptions bytes_two_branch_match_typable.

(* Source bool and uint8 must not be conflated by their common C translation. *)
Lemma packet_member_bool_not_uint8 : forall name,
  packet_member_type name [BeeTypes.Member_plain name (Vtype Tbool)] <>
    Some (Vtype (Tint I8 Unsigned noattr)).
Proof. intros name. simpl. destruct (ident_eq name name); [discriminate | contradiction]. Qed.

Lemma bytes_match_undeclared_schema_untypable :
  forall cenv Gamma Sigma scrutinee header schema fields rest yes no rt ef,
  PTree.get schema cenv = None ->
  ~ type_expr cenv Gamma Sigma
    (Match scrutinee [Pbytes header (Stype schema noattr) fields; Pbytes rest Bytes nil]
      [yes; no] rt) ef rt.
Proof.
  intros cenv Gamma Sigma scrutinee header schema fields rest yes no rt ef Hmissing Htyped.
  pose proof (type_infer_match_schemas _ _ _ _ _ _ _ _ _ Htyped) as Hschemas.
  inversion Hschemas as [|? ? Hschema Hrest]; subst.
  destruct Hschema as [co [Hlookup Hfacts]]. congruence.
Qed.

Print Assumptions packet_member_bool_not_uint8.
Print Assumptions bytes_match_undeclared_schema_untypable.

(* A source field type must not be reconstructed solely from its C type:
   bool and uint8 have the same representation.  Header.field typing still
   needs a source-member rule to preserve this distinction. *)
Lemma boolean_field_translation_loses_source_type :
  trans_ctype_btype (transBeePL_type (Vtype Tbool)) =
    Errors.OK (Vtype (Tint I8 Unsigned noattr)).
Proof. reflexivity. Qed.

Print Assumptions boolean_field_translation_loses_source_type.

Lemma source_field_preserves_bool : forall name,
  source_member_type name [BeeTypes.Member_plain name (Vtype Tbool)] = Errors.OK (Vtype Tbool).
Proof. intros name; simpl; destruct (ident_eq name name); [reflexivity |contradiction]. Qed.

Lemma optional_field_access_requires_match :
  forall cenv Gamma Sigma payload pt field ty ef,
  ~ type_expr cenv Gamma Sigma
    (Sfield (Val (Voption payload) (Ptrtype (Otype pt))) field ty) ef ty.
Proof.
  intros cenv Gamma Sigma payload pt field ty ef Htyped.
  destruct (type_infer_sfield _ _ _ _ _ _ _ _ Htyped)
    as [_ [sid [attr [co [ct [te [Hbase [Hkind Hrest]]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hbase) as Htype.
  cbn [typeof_expr] in Htype; subst te. destruct Hkind; discriminate.
Qed.

Print Assumptions source_field_preserves_bool.
Print Assumptions optional_field_access_requires_match.

(* Shape-typed code addresses now exist. The old function predicate requires
   EVERY such address to resolve, without runtime location evidence. This is
   overstrong; the checked callable-state invariant gates it by actual code
   locations instead. *)
Lemma legacy_function_requires_every_address : forall cenv Gamma Sigma bge vm m,
  well_formed_function cenv Gamma Sigma bge vm m ->
  forall b, exists fn,
    Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn).
Proof.
  intros cenv Gamma Sigma bge vm m Hwf b. inversion Hwf as [Hcontract].
  destruct (Hcontract b Ptrofs.zero nil (Ftype nil nil Utype false)
    nil nil Utype false nil nil ltac:(apply ty_valfun) ltac:(reflexivity)
    ltac:(constructor)) as [fn [Hfind Hrest]].
  exists fn. exact Hfind.
Qed.

Lemma legacy_function_missing_address_rejected : forall cenv Gamma Sigma (bge : BeePL.genv) vm m b,
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = None ->
  ~ well_formed_function cenv Gamma Sigma bge vm m.
Proof.
  intros cenv Gamma Sigma bge vm m b Hmissing Hwf.
  destruct (legacy_function_requires_every_address _ _ _ _ _ _ Hwf b) as [fn Hfind].
  congruence.
Qed.

Lemma legacy_store_missing_code_rejected : forall cenv Gamma Sigma (bge : BeePL.genv) vm m b,
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = None ->
  ~ store_well_typed cenv Gamma Sigma bge vm m.
Proof.
  intros cenv Gamma Sigma bge vm m b Hmissing [_ [_ Hfunctions]].
  eapply legacy_function_missing_address_rejected; eauto.
Qed.

(* The former empty-context progress counterexample is now rejected. *)
Theorem unbound_array_progress_regression : forall cenv Sigma arr,
  ~ type_expr cenv empty_context Sigma
    (Aaccess arr (Atype (Vtype (Tint I32 Signed noattr)) 1 noattr) 0
      (Vtype (Tint I32 Signed noattr))) nil (Vtype (Tint I32 Signed noattr)).
Proof. intros. apply unbound_array_access_rejected. apply PTree.gempty. Qed.

Print Assumptions legacy_function_requires_every_address.
Print Assumptions legacy_function_missing_address_rejected.
Print Assumptions legacy_store_missing_code_rejected.
Print Assumptions unbound_array_progress_regression.

Require Import Errors BeePL_typechecker.

Lemma unbound_array_checker_rejected : forall cenv Gamma Sigma arr ty index result,
  PTree.get arr Gamma = None ->
  exists error, type_check_expr cenv Gamma Sigma (Aaccess arr ty index result) = Error error.
Proof. intros. simpl. rewrite H. eexists; reflexivity. Qed.

Lemma bound_array_checker_accepts : forall cenv Sigma arr,
  let elem := Vtype (Tint I32 Signed noattr) in
  let ty := Atype elem 1 noattr in
  type_check_expr cenv (extend_context empty_context arr ty) Sigma
    (Aaccess arr ty 0 elem) = OK (elem, nil).
Proof. intros. simpl. unfold extend_context. rewrite PTree.gss. reflexivity. Qed.

Lemma out_of_bounds_array_checker_rejected : forall cenv Sigma arr,
  let elem := Vtype (Tint I32 Signed noattr) in
  let ty := Atype elem 1 noattr in
  exists error, type_check_expr cenv (extend_context empty_context arr ty) Sigma
    (Aaccess arr ty 1 elem) = Error error.
Proof. intros. simpl. unfold extend_context. rewrite PTree.gss. eexists; reflexivity. Qed.

Print Assumptions unbound_array_checker_rejected.
Print Assumptions bound_array_checker_accepts.
Print Assumptions out_of_bounds_array_checker_rejected.
