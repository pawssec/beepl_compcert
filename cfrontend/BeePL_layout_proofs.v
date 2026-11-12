(* Connect scalar initialization premises to CompCert composite layouts. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_initialization_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma translated_composite_lookup : forall env id,
  PTree.get id (bcomposite_composite_env env) =
    option_map bcomposite_ccomposite (PTree.get id env).
Proof.
  intros env. unfold bcomposite_composite_env.
  apply (@PTree_Properties.fold_rec bcomposite composite_env
    (fun after id co => PTree.set id (bcomposite_ccomposite co) after)
    (fun before after => forall id,
      PTree.get id after = option_map bcomposite_ccomposite (PTree.get id before))
    (PTree.empty composite) env).
  - intros before before' after Heq H id. rewrite <- Heq. apply H.
  - intros id. repeat rewrite PTree.gempty. reflexivity.
  - intros before after key co Hfresh Hin H id.
    repeat rewrite PTree.gsspec. destruct (peq id key); [reflexivity | apply H].
Qed.

Lemma translated_pointer_complete : forall env pt,
  Ctypes.complete_type env (transBeePL_ptr_type pt) = true.
Proof.
  intros env pt. induction pt as [bt a | pt IH | ts ef t v]; simpl; auto.
  destruct bt as [p | id a' | p n a']; try destruct p; reflexivity.
Qed.

(* Bytes is intrinsically complete in BeePL, but its C representation must
   actually be present. Keep this obligation visible until both environment
   builders agree on the reserved representation. *)
Lemma translated_type_complete : forall env,
  (exists co, PTree.get bytes_t env = Some co) ->
  forall t, Ctypes.complete_type (bcomposite_composite_env env)
    (transBeePL_type t) = bcomplete_type env t.
Proof.
  intros env [bytes Hbytes]. fix IH 1. intro t.
  destruct t as [|p|pt|id a|t n a|ts ef t v|]; simpl; auto.
  - destruct p; reflexivity.
  - apply translated_pointer_complete.
  - rewrite translated_composite_lookup. destruct (PTree.get id env); reflexivity.
  - rewrite translated_composite_lookup, Hbytes. reflexivity.
Qed.

Lemma translated_members_complete : forall env ms,
  (exists co, PTree.get bytes_t env = Some co) ->
  Ctypes.complete_members (bcomposite_composite_env env) (bmembers_cmembers ms) =
    bcomplete_members env ms.
Proof.
  intros env ms Hbytes. induction ms as [|m ms IH]; simpl; auto.
  rewrite IH. destruct m; simpl; try reflexivity.
  rewrite translated_type_complete by exact Hbytes. reflexivity.
Qed.

Lemma constructed_composite_consistent : forall env id su ms a co,
  bcomposite_of_def env id su ms a = OK co ->
  Ctypes.complete_members (bcomposite_composite_env env) (bmembers_cmembers ms) = true ->
  Ctypes.composite_consistent (bcomposite_composite_env env) (bcomposite_ccomposite co).
Proof.
  intros env id su ms a co Hbuild Hcomplete.
  apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  destruct (PTree.get id env); try discriminate.
  destruct (bcomplete_members env ms); try discriminate.
  inversion Hbuild; subst. constructor; simpl; auto.
Qed.

Lemma constructed_composite_consistent_with_bytes : forall env id su ms a co,
  (exists bytes, PTree.get bytes_t env = Some bytes) ->
  bcomposite_of_def env id su ms a = OK co ->
  Ctypes.composite_consistent (bcomposite_composite_env env) (bcomposite_ccomposite co).
Proof.
  intros env id su ms a co Hbytes Hbuild.
  eapply constructed_composite_consistent; eauto.
  rewrite translated_members_complete by exact Hbytes.
  apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  destruct (PTree.get id env); try discriminate.
  destruct (bcomplete_members env ms); congruence.
Qed.

Lemma primitive_translation_inverse : forall ct pt,
  trans_ctype_btype ct = OK (Vtype pt) -> ct = transBeePL_type (Vtype pt).
Proof.
  intros ct pt H. destruct ct; simpl in H; try discriminate;
    try (inversion H; reflexivity).
  destruct ct; discriminate.
Qed.

Lemma unchanged_nonvolatile_attributes : forall ct,
  Ctypes.change_attributes (Ctyping.attr_add_volatile false) ct = ct.
Proof.
  intros ct. destruct ct; simpl; try reflexivity;
    destruct a as [v al]; destruct v; reflexivity.
Qed.

Lemma primitive_member_type_from_typing : forall ms name pt ct,
  Ctyping.type_of_member (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) name ms = OK ct ->
  trans_ctype_btype ct = OK (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  field_type name ms = OK (transBeePL_type (Vtype pt)).
Proof.
  intros ms name pt ct Hlookup Hconvert Hnonvolatile.
  assert (Hattr : attr_volatile (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) = false).
  { destruct pt as [|sz sign a|sign a]; try destruct sz; try destruct sign; exact Hnonvolatile. }
  unfold Ctyping.type_of_member in Hlookup. rewrite Hattr in Hlookup.
  destruct (field_type name ms) as [found|err] eqn:Hfound; try discriminate.
  simpl in Hlookup. rewrite unchanged_nonvolatile_attributes in Hlookup.
  inversion Hlookup; subst. rewrite (primitive_translation_inverse _ _ Hconvert).
  reflexivity.
Qed.

Lemma planned_member_types_from_typing : forall fs ms cts,
  type_of_members
    (combine (List.map Ctypes.attr_of_type
      (transBeePL_types transBeePL_type (List.map (fun f => Vtype (planned_type f)) fs)))
      (List.map planned_field fs)) ms = OK cts ->
  trans_ctypes_btypes trans_ctype_btype cts =
    OK (List.map (fun f => Vtype (planned_type f)) fs) ->
  (forall f, In f fs -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false) ->
  forall f, In f fs ->
    field_type (planned_field f) ms = OK (transBeePL_type (Vtype (planned_type f))).
Proof.
  induction fs as [|head fs IH]; intros ms cts Hlookup Hconvert Hnonvolatile f Hin;
    [contradiction |].
  cbn [List.map transBeePL_types combine type_of_members] in Hlookup.
  destruct (Ctyping.type_of_member
    (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type head))))
    (planned_field head) ms) as [ct|err] eqn:Hhead; try discriminate.
  simpl in Hlookup.
  destruct (type_of_members _ ms) as [rest|err] eqn:Hrest; try discriminate.
  inversion Hlookup; subst cts. simpl in Hconvert.
  destruct (trans_ctype_btype ct) as [bt|err] eqn:Hct; try discriminate.
  destruct (trans_ctypes_btypes trans_ctype_btype rest) as [bts|err] eqn:Hcts; try discriminate.
  inversion Hconvert; subst bt bts.
  destruct Hin as [Heq | Hin].
  - subst f. eapply primitive_member_type_from_typing; eauto.
    apply Hnonvolatile. left; reflexivity.
  - eapply IH; [exact Hrest | exact Hcts | | exact Hin].
    intros other Hother. apply Hnonvolatile. right; exact Hother.
Qed.

Lemma source_member_type_translation : forall members field ty,
  source_member_type field members = OK ty ->
  field_type field (bmembers_cmembers members) = OK (transBeePL_type ty).
Proof.
  induction members as [|member rest IH]; intros field ty H; [discriminate |].
  destruct member; simpl in H |- *; destruct (ident_eq field i); simpl in *;
    try (apply IH; exact H); inversion H; subst; try reflexivity.
  destruct (zlt z (bitsize_intsize i0)); reflexivity.
Qed.

Lemma source_planned_member_types : forall fs members,
  source_member_types (List.map planned_field fs) members =
    OK (List.map (fun f => Vtype (planned_type f)) fs) ->
  forall f, In f fs -> source_member_type (planned_field f) members = OK (Vtype (planned_type f)).
Proof.
  induction fs as [|head rest IH]; intros members H f Hin; [contradiction |].
  simpl in H. destruct (source_member_type (planned_field head) members) as [ty|err] eqn:Hhead;
    try discriminate.
  destruct (source_member_types (List.map planned_field rest) members) as [tys|err] eqn:Hrest;
    try discriminate.
  inversion H; subst ty tys. destruct Hin as [<- | Hin]; [exact Hhead |].
  eapply IH; eauto.
Qed.

Lemma typed_structure_plan_facts : forall cenv Gamma Sigma sid sa pa fs ef co,
  type_expr cenv Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  PTree.get sid cenv = Some co ->
  (forall f, In f fs -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false) ->
  forall f, In f fs ->
    typeof_value (planned_value f) (Vtype (planned_type f)) /\
    field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype (planned_type f))).
Proof.
  intros cenv Gamma Sigma sid sa pa fs ef co Htyped Hco Hnonvolatile.
  inversion Htyped; subst.
  match goal with
  | Hargs : type_exprs _ _ _ (planned_expressions fs) _ _ |- _ =>
      destruct (typed_planned_arguments _ _ _ _ _ _ Hargs) as [Htypes Hvalues]
  end.
  subst bts.
  assert (co0 = co) by congruence. subst co0.
  intros f Hin. split; [apply Hvalues; exact Hin |].
  apply source_member_type_translation. eapply source_planned_member_types; eauto.
Qed.

Definition source_composites_consistent (env : bcomposite_env) : Prop :=
  forall id co, PTree.get id env = Some co ->
    Ctypes.composite_consistent (bcomposite_composite_env env) (bcomposite_ccomposite co).

Lemma translated_environment_extension : forall env env',
  (forall id co, PTree.get id env = Some co -> PTree.get id env' = Some co) ->
  forall id co, PTree.get id (bcomposite_composite_env env) = Some co ->
    PTree.get id (bcomposite_composite_env env') = Some co.
Proof.
  intros env env' Hext id co Hget.
  rewrite translated_composite_lookup in Hget |- *.
  destruct (PTree.get id env) as [bco|] eqn:Hb; try discriminate.
  rewrite (Hext id bco Hb). exact Hget.
Qed.

Lemma constructed_composite_fresh : forall env id su ms a co,
  bcomposite_of_def env id su ms a = OK co -> PTree.get id env = None.
Proof.
  intros env id su ms a co Hbuild. apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  destruct (PTree.get id env); congruence.
Qed.

Lemma consistent_composite_extension : forall env id co,
  PTree.get id env = None -> source_composites_consistent env ->
  Ctypes.composite_consistent (bcomposite_composite_env env) (bcomposite_ccomposite co) ->
  source_composites_consistent (PTree.set id co env).
Proof.
  intros env id co Hfresh Henv Hco.
  assert (Hext : forall key old, PTree.get key env = Some old ->
    PTree.get key (PTree.set id co env) = Some old).
  { intros key old Hget. rewrite PTree.gso; auto. congruence. }
  intros key found Hget.
  eapply Ctypes.composite_consistent_stable.
  - apply translated_environment_extension. exact Hext.
  - rewrite PTree.gsspec in Hget. destruct (peq key id).
    + inversion Hget; subst. exact Hco.
    + eapply Henv; eauto.
Qed.

Lemma add_source_composites_consistent : forall defs env env',
  add_bcomposite_definitions env defs = OK env' ->
  source_composites_consistent env ->
  (exists bytes, PTree.get bytes_t env = Some bytes) ->
  source_composites_consistent env'.
Proof.
  induction defs as [|[id su ms a] defs IH]; intros env env' Hbuild Henv Hbytes.
  - simpl in Hbuild. inversion Hbuild; subst. exact Henv.
  - simpl in Hbuild.
    destruct (bcomposite_of_def env id su ms a) as [co|err] eqn:Hco; try discriminate.
    eapply IH; [exact Hbuild | |].
    + apply consistent_composite_extension; auto.
      * eapply constructed_composite_fresh; eauto.
      * eapply constructed_composite_consistent_with_bytes; eauto.
    + destruct Hbytes as [bytes Hbytes]. exists bytes.
      rewrite PTree.gso; auto.
      pose proof (constructed_composite_fresh _ _ _ _ _ _ Hco). congruence.
Qed.

Theorem built_source_composites_consistent : forall defs env,
  build_bcomposite_env defs = OK env -> source_composites_consistent env.
Proof.
  intros defs env Hbuild.
  unfold build_bcomposite_env in Hbuild. simpl in Hbuild.
  eapply add_source_composites_consistent; [exact Hbuild | |].
  - apply consistent_composite_extension.
    + apply PTree.gempty.
    + intros id co Hget. rewrite PTree.gempty in Hget. discriminate.
    + constructor; reflexivity.
  - eexists. apply PTree.gss.
Qed.

Theorem program_composites_consistent : forall p,
  source_composites_consistent p.(prog_comp_env).
Proof. intro p. eapply built_source_composites_consistent. apply prog_comp_env_eq. Qed.

Theorem built_translated_composites_consistent : forall defs env,
  build_bcomposite_env defs = OK env ->
  Ctypes.composite_env_consistent (bcomposite_composite_env env).
Proof.
  intros defs env Hbuild id co Hget. rewrite translated_composite_lookup in Hget.
  destruct (PTree.get id env) as [bco|] eqn:Hb; try discriminate.
  inversion Hget; subst. eapply built_source_composites_consistent; eauto.
Qed.

Lemma add_source_composites_preserves : forall defs env env',
  add_bcomposite_definitions env defs = OK env' ->
  forall id co, PTree.get id env = Some co -> PTree.get id env' = Some co.
Proof.
  induction defs as [|[key su ms a] defs IH]; intros env env' Hbuild id co Hget.
  - simpl in Hbuild. inversion Hbuild; subst. exact Hget.
  - simpl in Hbuild.
    destruct (bcomposite_of_def env key su ms a) as [new|err] eqn:Hnew; try discriminate.
    eapply IH; [exact Hbuild |]. rewrite PTree.gso; auto.
    pose proof (constructed_composite_fresh _ _ _ _ _ _ Hnew). congruence.
Qed.

Lemma built_source_bytes_present : forall defs env,
  build_bcomposite_env defs = OK env -> exists co, PTree.get bytes_t env = Some co.
Proof.
  intros defs env Hbuild. unfold build_bcomposite_env in Hbuild. simpl in Hbuild.
  eexists. eapply add_source_composites_preserves; [exact Hbuild | apply PTree.gss].
Qed.

(* Successful source construction guarantees the member shape interpreted by
   field evaluation, independently of the compiler's more general C metadata. *)
Definition bmember_is_plain (member : bmember) : Prop :=
  match member with Member_plain _ _ => True | _ => False end.

Lemma safe_members_plain : forall env members,
  bmembers_layout_safe env members = true -> Forall bmember_is_plain members.
Proof.
  intros env members. induction members as [|member rest IH]; intros Hsafe;
    [constructor|].
  destruct member; simpl in Hsafe; try discriminate.
  apply Bool.andb_true_iff in Hsafe as [Hhead Htail]. constructor; [exact I|auto].
Qed.

Lemma constructed_composite_shape : forall env id su members attr co,
  bcomposite_of_def env id su members attr = OK co ->
  co.(co_su) = Struct /\ Forall bmember_is_plain co.(co_members).
Proof.
  intros env id su members attr co Hbuild.
  pose proof (bcomposite_of_def_layout_safe _ _ _ _ _ _ Hbuild) as Hsafe.
  apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  destruct (PTree.get id env); try discriminate.
  destruct (bcomplete_members env members); try discriminate.
  inversion Hbuild; subst co. simpl.
  destruct su; simpl in Hsafe; try discriminate. split; [reflexivity|].
  apply Bool.andb_true_iff in Hsafe as [Hmembers Halign].
  eapply safe_members_plain; exact Hmembers.
Qed.

Lemma added_composites_shape : forall defs env final,
  add_bcomposite_definitions env defs = OK final ->
  (forall id co, PTree.get id env = Some co ->
    co.(co_su) = Struct /\ Forall bmember_is_plain co.(co_members)) ->
  forall id co, PTree.get id final = Some co ->
    co.(co_su) = Struct /\ Forall bmember_is_plain co.(co_members).
Proof.
  induction defs as [|[key su members attr] rest IH]; intros env final Hbuild Henv id co Hget.
  - simpl in Hbuild. inversion Hbuild; subst. eauto.
  - simpl in Hbuild.
    destruct (bcomposite_of_def env key su members attr) as [fresh|err] eqn:Hfresh;
      try discriminate.
    eapply IH; [exact Hbuild| |exact Hget].
    intros name found Hfound. rewrite PTree.gsspec in Hfound.
    destruct (peq name key).
    + inversion Hfound; subst. eapply constructed_composite_shape; exact Hfresh.
    + eauto.
Qed.

Theorem program_composite_shape : forall p id co,
  PTree.get id p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct /\ Forall bmember_is_plain co.(co_members).
Proof.
  intros p id co Hget.
  eapply added_composites_shape; [exact (prog_comp_env_eq p)| |exact Hget].
  intros name found Hfound. rewrite PTree.gempty in Hfound. discriminate.
Qed.

Print Assumptions program_composite_shape.

Corollary program_type_completeness : forall p t,
  Ctypes.complete_type (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type t) =
    bcomplete_type p.(prog_comp_env) t.
Proof.
  intros p t. apply translated_type_complete.
  eapply built_source_bytes_present. apply prog_comp_env_eq.
Qed.

(* The same single-Bytes-field input that exposed the unseeded builder now
   receives space for both pointers through the public program builder. *)
Lemma built_bytes_field_layout : exists env co,
  build_bcomposite_env
    [Bcomposite 2%positive Struct [Member_plain 1%positive Bytes] noattr] = OK env /\
  PTree.get 2%positive env = Some co /\
  co.(co_sizeof) = 2 * (if Archi.ptr64 then 8 else 4).
Proof. eexists; eexists. split; [reflexivity |]. split; reflexivity. Qed.

Lemma primitive_chunk_size_translation : forall env pt,
  size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) =
    Ctypes.sizeof env (transBeePL_type (Vtype pt)).
Proof. intros env [|sz sign a|sign a]; try destruct sz; try destruct sign; reflexivity. Qed.

Lemma primitive_chunk_positive : forall pt,
  0 < size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)).
Proof. intros [|sz sign a|sign a]; try destruct sz; try destruct sign; simpl; lia. Qed.

Lemma consistent_struct_size_bound : forall env co,
  Ctypes.composite_consistent env (bcomposite_ccomposite co) ->
  co.(co_su) = Struct ->
  Ctypes.sizeof_struct env (bmembers_cmembers co.(co_members)) <= co.(co_sizeof).
Proof.
  intros env co Hconsistent Hstruct.
  pose proof (Ctypes.co_consistent_sizeof _ _ Hconsistent) as Hsize.
  simpl in Hsize. rewrite Hstruct in Hsize. simpl in Hsize. rewrite Hsize.
  apply align_le. destruct (co_alignof_two_p co) as [n Hn]. rewrite Hn.
  apply two_power_nat_pos.
Qed.

Lemma primitive_field_layout_bounds : forall env sid co name delta pt,
  PTree.get sid env = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env env) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  field_offset (bcomposite_composite_env env) name (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  field_type name (bmembers_cmembers co.(co_members)) = OK (transBeePL_type (Vtype pt)) ->
  (align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) |
    Ctypes.alignof (bcomposite_composite_env env) (transBeePL_type (Vtype pt))) ->
  0 <= Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta)) /\
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta)) +
    size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) <= sizeof_type env (Stype sid noattr) /\
  (align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)) |
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta))).
Proof.
  intros env sid co name delta pt Hco Hconsistent Hstruct Hrepresent Hoffset Htype Halign.
  pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Htype) as [Hlo Hhi].
  pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as Hsize.
  pose proof (primitive_chunk_positive pt) as Hpositive.
  pose proof (primitive_chunk_size_translation (bcomposite_composite_env env) pt) as Hwidth.
  assert (Hdelta : 0 <= delta <= Ptrofs.max_unsigned) by lia.
  rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr by exact Hdelta.
  split; [exact Hlo |]. split.
  - simpl. rewrite Hco. lia.
  - eapply Z.divide_trans; [exact Halign |]. eapply Ctypes.field_offset_aligned; eauto.
Qed.

Print Assumptions translated_composite_lookup.
Print Assumptions primitive_field_layout_bounds.

Lemma primitive_field_offset_representable : forall env co name delta pt,
  Ctypes.composite_consistent env (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  field_offset env name (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  field_type name (bmembers_cmembers co.(co_members)) = OK (transBeePL_type (Vtype pt)) ->
  0 <= delta <= Ptrofs.max_unsigned.
Proof.
  intros env co name delta pt Hconsistent Hstruct Hrepresent Hoffset Htype.
  pose proof (Ctypes.field_offset_in_range _ _ _ _ _ Hoffset Htype) as [Hlo Hhi].
  pose proof (consistent_struct_size_bound _ _ Hconsistent Hstruct) as Hsize.
  pose proof (primitive_chunk_size_translation env pt) as Hwidth.
  pose proof (primitive_chunk_positive pt) as Hpositive. lia.
Qed.

Lemma primitive_fields_do_not_overlap : forall env members name1 delta1 pt1 name2 delta2 pt2,
  field_offset env name1 members = OK (delta1, Full) ->
  field_type name1 members = OK (transBeePL_type (Vtype pt1)) ->
  field_offset env name2 members = OK (delta2, Full) ->
  field_type name2 members = OK (transBeePL_type (Vtype pt2)) ->
  name1 <> name2 ->
  0 <= delta1 <= Ptrofs.max_unsigned -> 0 <= delta2 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta1)) +
    size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt1)) <=
      Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta2)) \/
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta2)) +
    size_chunk (transl_bchunk_cchunk (chunk_of_ptype pt2)) <=
      Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta1)).
Proof.
  intros env members name1 delta1 pt1 name2 delta2 pt2 Hoffset1 Htype1 Hoffset2 Htype2 Hneq Hrange1 Hrange2.
  pose proof (Ctypes.field_offset_no_overlap _ _ _ _ _ _ _ _ _ _
    Hoffset1 Htype1 Hoffset2 Htype2 Hneq) as Hseparation.
  unfold layout_start, layout_width, bitsizeof in Hseparation.
  pose proof (primitive_chunk_size_translation env pt1) as Hwidth1.
  pose proof (primitive_chunk_size_translation env pt2) as Hwidth2.
  rewrite !Ptrofs.add_zero_l, !Ptrofs.unsigned_repr by lia.
  destruct Hseparation; [left | right]; lia.
Qed.

Lemma primitive_field_plan_bounds : forall bge sid co fs,
  PTree.get sid bge.(genv_cenv) = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env bge.(genv_cenv)) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  (forall f, In f fs ->
    field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype (planned_type f)))) ->
  (forall f, In f fs ->
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) |
     Ctypes.alignof (bcomposite_composite_env bge.(genv_cenv)) (transBeePL_type (Vtype (planned_type f))))) ->
  forall f, In f fs ->
    0 <= planned_start Ptrofs.zero f /\
    planned_end Ptrofs.zero f <= sizeof_type bge.(genv_cenv) (Stype sid noattr) /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f).
Proof.
  intros bge sid co fs Hco Hconsistent Hstruct Hrepresent Hplans Htypes Halign f Hin.
  destruct (Hplans f Hin) as [co' [Hco' [Hoffset Hrest]]].
  assert (co' = co) by congruence. subst co'.
  eapply primitive_field_layout_bounds; eauto.
Qed.

Lemma primitive_field_plan_separation : forall bge sid co fs,
  PTree.get sid bge.(genv_cenv) = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env bge.(genv_cenv)) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  (forall f, In f fs ->
    field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype (planned_type f)))) ->
  NoDup (List.map planned_field fs) -> field_plans_separated Ptrofs.zero fs.
Proof.
  intros bge sid co fs Hco Hconsistent Hstruct Hrepresent.
  induction fs as [|f fs IH]; intros Hplans Htypes Hdistinct; [exact I |].
  inversion Hdistinct as [|name names Hnotin Htail]; subst. split.
  - intros other Hin.
    destruct (Hplans f (or_introl eq_refl)) as [co1 [Hco1 [Hoffset1 Hrest1]]].
    destruct (Hplans other (or_intror Hin)) as [co2 [Hco2 [Hoffset2 Hrest2]]].
    assert (co1 = co) by congruence. assert (co2 = co) by congruence. subst co1 co2.
    assert (Hneq : planned_field f <> planned_field other).
    { intro Heq. apply Hnotin. rewrite Heq. apply in_map. exact Hin. }
    assert (Hrange1 : 0 <= planned_offset f <= Ptrofs.max_unsigned).
    { eapply primitive_field_offset_representable; eauto. apply Htypes. left; reflexivity. }
    assert (Hrange2 : 0 <= planned_offset other <= Ptrofs.max_unsigned).
    { eapply primitive_field_offset_representable; eauto. apply Htypes. right; exact Hin. }
    eapply primitive_fields_do_not_overlap; eauto.
    + apply Htypes. left; reflexivity.
    + apply Htypes. right; exact Hin.
  - apply IH; auto; intros other Hin; [apply Hplans | apply Htypes]; right; exact Hin.
Qed.

Print Assumptions primitive_fields_do_not_overlap.
Print Assumptions primitive_field_plan_bounds.
Print Assumptions primitive_field_plan_separation.

Lemma primitive_default_alignment : forall env pt,
  Archi.align_int64 = 8 ->
  attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype pt))) = None ->
  Ctypes.alignof env (transBeePL_type (Vtype pt)) =
    align_chunk (transl_bchunk_cchunk (chunk_of_ptype pt)).
Proof.
  intros env [|sz sign a|sign a] Hlong Hattr; simpl in *.
  - reflexivity.
  - unfold align_attr. rewrite Hattr. destruct sz, sign; reflexivity.
  - unfold align_attr. rewrite Hattr, Hlong. reflexivity.
Qed.

Lemma primitive_structure_progress_from_layout :
  forall bge cenv Sigma layout p vm m sid sa pa fs co,
  typed_memory_layout cenv Sigma layout m ->
  PTree.get sid bge.(genv_cenv) = Some co ->
  Ctypes.composite_consistent (bcomposite_composite_env bge.(genv_cenv)) (bcomposite_ccomposite co) ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  Archi.align_int64 = 8 ->
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  (forall f, In f fs ->
    field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype (planned_type f)))) ->
  (forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (List.map planned_field fs) ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa)) = (allocated, b) /\
    ssem_expr bge p vm m
      (Sinit sid (List.map planned_field fs) (planned_expressions fs)
        (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout cenv Sigma (extend_field_layout layout b Ptrofs.zero fs) m'.
Proof.
  intros bge cenv Sigma layout p vm m sid sa pa fs co Hmemory Hco Hconsistent Hstruct Hrepresent
    Hlong Hplans Htypes Hattrs Hdistinct.
  eapply primitive_structure_initialization_progress; [exact Hmemory | exact Hplans | |].
  - eapply primitive_field_plan_separation; eauto.
  - intros f Hin. eapply primitive_field_plan_bounds; eauto.
    intros field Hfield.
    rewrite (primitive_default_alignment (bcomposite_composite_env bge.(genv_cenv))
      (planned_type field) Hlong (Hattrs field Hfield)). apply Z.divide_refl.
Qed.

Print Assumptions primitive_default_alignment.
Print Assumptions primitive_structure_progress_from_layout.

Corollary program_primitive_structure_progress :
  forall cenv Sigma layout p vm m sid sa pa fs co,
  typed_memory_layout cenv Sigma layout m ->
  PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  Archi.align_int64 = 8 ->
  (forall f, In f fs -> field_plan_valid (globalenv p) sid f) ->
  (forall f, In f fs ->
    field_type (planned_field f) (bmembers_cmembers co.(co_members)) =
      OK (transBeePL_type (Vtype (planned_type f)))) ->
  (forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (List.map planned_field fs) ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (allocated, b) /\
    ssem_expr (globalenv p) p vm m
      (Sinit sid (List.map planned_field fs) (planned_expressions fs)
        (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout cenv Sigma (extend_field_layout layout b Ptrofs.zero fs) m'.
Proof.
  intros cenv Sigma layout p vm m sid sa pa fs co Hmemory Hco Hstruct Hsize
    Halign Hplans Htypes Hattrs Hdistinct.
  eapply (primitive_structure_progress_from_layout (globalenv p) cenv Sigma layout
    p vm m sid sa pa fs co); eauto.
  exact (program_composites_consistent p sid co Hco).
Qed.

Print Assumptions program_primitive_structure_progress.

Corollary typed_primitive_structure_progress :
  forall Gamma Sigma layout p vm m sid sa pa fs ef co,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> co.(co_sizeof) <= Ptrofs.max_unsigned ->
  Archi.align_int64 = 8 ->
  (forall f, In f fs ->
    field_offset (bcomposite_composite_env p.(prog_comp_env)) (planned_field f)
      (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full)) ->
  (forall f, In f fs -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false) ->
  (forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (List.map planned_field fs) ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (allocated, b) /\
    ssem_expr (globalenv p) p vm m
      (Sinit sid (List.map planned_field fs) (planned_expressions fs)
        (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout p.(prog_comp_env) Sigma (extend_field_layout layout b Ptrofs.zero fs) m'.
Proof.
  intros Gamma Sigma layout p vm m sid sa pa fs ef co Htyped Hmemory Hco Hstruct Hsize
    Halign Hoffsets Hnonvolatile Hattrs Hdistinct.
  pose proof (typed_structure_plan_facts _ _ _ _ _ _ _ _ _ Htyped Hco Hnonvolatile) as Hfacts.
  eapply (program_primitive_structure_progress p.(prog_comp_env) Sigma layout
    p vm m sid sa pa fs co); eauto.
  - intros f Hin. exists co. split; [exact Hco |].
    split; [apply Hoffsets; exact Hin |].
    split; [exact (proj1 (Hfacts f Hin)) | apply Hnonvolatile; exact Hin].
  - intros f Hin. exact (proj2 (Hfacts f Hin)).
Qed.

Print Assumptions primitive_translation_inverse.
Print Assumptions primitive_member_type_from_typing.
Print Assumptions planned_member_types_from_typing.
Print Assumptions typed_structure_plan_facts.
Print Assumptions typed_primitive_structure_progress.

(* Target regression: the 64-bit BPF configuration formerly used the 32-bit
   integer alignment. These checks also apply to other configured 64-bit targets. *)
Lemma native_64_bit_integer_alignment :
  Archi.ptr64 = true -> Archi.align_int64 = 8.
Proof. vm_compute. congruence. Qed.

Lemma native_64_bit_mixed_field_offset : Archi.ptr64 = true ->
  Ctypes.field_offset (PTree.empty Ctypes.composite) 2%positive
    [Ctypes.Member_plain 1%positive (Ctypes.Tint I32 Unsigned noattr);
     Ctypes.Member_plain 2%positive (Ctypes.Tlong Unsigned noattr)] = OK (8, Full).
Proof. vm_compute. congruence. Qed.

Print Assumptions native_64_bit_integer_alignment.
Print Assumptions native_64_bit_mixed_field_offset.
Print Assumptions translated_type_complete.
Print Assumptions translated_members_complete.
Print Assumptions constructed_composite_consistent.
Print Assumptions constructed_composite_consistent_with_bytes.
Print Assumptions built_source_composites_consistent.
Print Assumptions program_composites_consistent.
Print Assumptions built_translated_composites_consistent.
Print Assumptions built_bytes_field_layout.
Print Assumptions program_type_completeness.



Theorem object_type_at_within_allocation : forall cenv Sigma block offset ty,
  object_type_at cenv Sigma block offset ty ->
  exists stored,
    PTree.get block Sigma = Some stored /\
    0 <= offset /\ 0 <= sizeof_type cenv ty /\
    offset + sizeof_type cenv ty <= sizeof_type cenv (stored_object_type stored).
Proof.
  intros cenv Sigma block offset ty Hobject. induction Hobject.
  - exists stored. repeat split; try assumption; lia.
  - destruct IHHobject as [stored [Hstored [Hbase [Hsize Hbound]]]].
    exists stored. repeat split; try assumption; lia.
  - destruct IHHobject as [stored [Hstored [Hbase [Hsize Hbound]]]].
    exists stored. cbn [sizeof_type] in Hbound.
    rewrite Z.max_r in Hbound by lia. repeat split; try assumption; nia.
Qed.

Theorem object_type_at_readable_subrange : forall cenv Sigma block offset ty stored m,
  object_type_at cenv Sigma block offset ty ->
  PTree.get block Sigma = Some stored ->
  Mem.range_perm m block 0 (sizeof_type cenv (stored_object_type stored)) Cur Readable ->
  Mem.range_perm m block offset (offset + sizeof_type cenv ty) Cur Readable.
Proof.
  intros cenv Sigma block offset ty stored m Hobject Hstored Hread.
  destruct (object_type_at_within_allocation _ _ _ _ _ Hobject)
    as [root [Hroot [Hoffset [Hsize Hbound]]]].
  assert (root = stored) by congruence. subst root.
  unfold Mem.range_perm in *. intros byte Hbyte. apply Hread. lia.
Qed.

Lemma object_type_at_offset_no_wrap : forall cenv Sigma block offset ty stored,
  object_type_at cenv Sigma block offset ty ->
  PTree.get block Sigma = Some stored ->
  sizeof_type cenv (stored_object_type stored) <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.repr offset) = offset.
Proof.
  intros cenv Sigma block offset ty stored Hobject Hstored Hrepresentable.
  destruct (object_type_at_within_allocation _ _ _ _ _ Hobject)
    as [root [Hroot [Hoffset [Hsize Hbound]]]].
  assert (root = stored) by congruence. subst root.
  apply Ptrofs.unsigned_repr. lia.
Qed.

Print Assumptions object_type_at_store_extension.
Print Assumptions object_type_at_within_allocation.
Print Assumptions object_type_at_readable_subrange.
Print Assumptions object_type_at_offset_no_wrap.

Lemma typed_struct_value_layout : forall cenv Gamma Sigma v annotation ef id a,
  type_expr cenv Gamma Sigma (Val v annotation) ef (Stype id a) ->
  exists b ofs, v = Vloc b ofs /\ annotation = Stype id a /\
    object_type_at cenv Sigma b (Ptrofs.unsigned ofs) (Stype id a).
Proof. intros; inversion H; subst; eauto 8. Qed.

Lemma typed_bytes_value_layout : forall cenv Gamma Sigma v annotation ef,
  type_expr cenv Gamma Sigma (Val v annotation) ef Bytes ->
  exists b ofs, v = Vloc b ofs /\ annotation = Bytes /\
    object_type_at cenv Sigma b (Ptrofs.unsigned ofs) Bytes.
Proof. intros; inversion H; subst; eauto 8. Qed.

Lemma typed_struct_requires_allocation : forall cenv Gamma Sigma b ofs id a ef,
  type_expr cenv Gamma Sigma (Val (Vloc b ofs) (Stype id a)) ef (Stype id a) ->
  exists stored, PTree.get b Sigma = Some stored /\
    Ptrofs.unsigned ofs + sizeof_type cenv (Stype id a) <=
      sizeof_type cenv (stored_object_type stored).
Proof.
  intros cenv Gamma Sigma b ofs id a ef Htyped. inversion Htyped; subst.
  match goal with Hobject : object_type_at _ _ _ _ _ |- _ =>
    destruct (object_type_at_within_allocation _ _ _ _ _ Hobject)
      as [stored [Hroot [Hoffset [Hsize Hbound]]]]
  end. exists stored; auto.
Qed.

Lemma typed_bytes_requires_allocation : forall cenv Gamma Sigma b ofs ef,
  type_expr cenv Gamma Sigma (Val (Vloc b ofs) Bytes) ef Bytes ->
  exists stored, PTree.get b Sigma = Some stored /\
    Ptrofs.unsigned ofs + sizeof_type cenv Bytes <=
      sizeof_type cenv (stored_object_type stored).
Proof.
  intros cenv Gamma Sigma b ofs ef Htyped. inversion Htyped; subst.
  match goal with Hobject : object_type_at _ _ _ _ _ |- _ =>
    destruct (object_type_at_within_allocation _ _ _ _ _ Hobject)
      as [stored [Hroot [Hoffset [Hsize Hbound]]]]
  end. exists stored; auto.
Qed.

Print Assumptions typed_struct_value_layout.
Print Assumptions typed_bytes_value_layout.
Print Assumptions typed_struct_requires_allocation.
Print Assumptions typed_bytes_requires_allocation.
