(* Alignment validation is executable at the public builder. The former
   offset-one Bytes witness is rejected; safe strengthening remains accepted. *)
Require Import List Bool ZArith Lia Coqlib AST Maps Memory Memdata Integers Ctypes Errors.
Require Import BeeTypes BeePL BeePL_object_paths BeePL_layout_proofs.
Import ListNotations.
Local Open Scope Z_scope.

Definition weakened_packet_alignment : attr :=
  {| attr_volatile := false; attr_alignas := Some 0%N |}.
Definition strengthened_packet_alignment : attr :=
  {| attr_volatile := false; attr_alignas := Some 4%N |}.
Definition packet_alignment_definitions : list bcomposite_definition :=
  [Bcomposite 101%positive Struct [Member_plain 105%positive Bytes] noattr;
   Bcomposite 102%positive Struct
     [Member_plain 103%positive (Vtype (Tint I8 Unsigned noattr));
      Member_plain 104%positive (Stype 101%positive weakened_packet_alignment)] noattr].

Theorem packet_alignment_builder_rejects_weakened_use :
  exists error, build_bcomposite_env packet_alignment_definitions = Error error.
Proof. eexists; vm_compute; reflexivity. Qed.

Example packet_alignment_builder_rejects_weakened_definition :
  exists error, build_bcomposite_env
    [Bcomposite 101%positive Struct [Member_plain 105%positive Bytes]
      weakened_packet_alignment] = Error error.
Proof. eexists; vm_compute; reflexivity. Qed.

Example packet_alignment_builder_accepts_overaligned_element :
  exists env, build_bcomposite_env
    [Bcomposite 101%positive Struct
      [Member_plain 105%positive
        (Atype (Vtype (Tint I8 Unsigned strengthened_packet_alignment)) 2 noattr)] noattr]
      = OK env.
Proof. eexists; vm_compute; reflexivity. Qed.

Example packet_alignment_builder_accepts_safe_strengthening :
  exists env, build_bcomposite_env
    [Bcomposite 101%positive Struct [Member_plain 105%positive Bytes]
       strengthened_packet_alignment;
     Bcomposite 102%positive Struct
       [Member_plain 104%positive
         (Atype (Stype 101%positive strengthened_packet_alignment) 2 noattr)] noattr] = OK env.
Proof. eexists; vm_compute; reflexivity. Qed.

Example packet_alignment_builder_accepts_reference_to_unfinished_type :
  exists env, build_bcomposite_env
    [Bcomposite 101%positive Struct
      [Member_plain 105%positive (Ptrtype (Reftype (Bstruct 102%positive noattr) noattr))]
      noattr] = OK env.
Proof. eexists; vm_compute; reflexivity. Qed.

Example inline_unit_array_alignment_retained : forall env,
  btype_inline_alignment_safe env (Atype Utype 3 noattr) = true.
Proof. reflexivity. Qed.

Lemma local_alignment_guard_facts : forall env ty,
  btype_local_alignment_safe env ty = true ->
  Ctypes.alignof (bcomposite_composite_env env)
    (Ctypes.remove_attributes (transBeePL_type ty)) <=
    Ctypes.alignof (bcomposite_composite_env env) (transBeePL_type ty).
Proof. intros env ty H. apply Z.leb_le; exact H. Qed.

Theorem inline_alignment_guard_local : forall env ty,
  btype_inline_alignment_safe env ty = true ->
  Ctypes.alignof (bcomposite_composite_env env)
    (Ctypes.remove_attributes (transBeePL_type ty)) <=
    Ctypes.alignof (bcomposite_composite_env env) (transBeePL_type ty).
Proof.
  intros env ty H. apply local_alignment_guard_facts.
  destruct ty; apply andb_true_iff in H; tauto.
Qed.

Theorem inline_alignment_guard_array : forall env elem len attr,
  btype_inline_alignment_safe env (Atype elem len attr) = true ->
  btype_inline_alignment_safe env elem = true.
Proof. intros env elem len attr H. apply andb_true_iff in H; tauto. Qed.

Theorem accepted_member_alignment_guard : forall env members id ty,
  bmembers_layout_safe env members = true ->
  In (Member_plain id ty) members -> btype_inline_alignment_safe env ty = true.
Proof.
  intros env members; induction members as [|member rest IH]; intros id ty Hsafe Hin;
    [contradiction|].
  destruct member; simpl in Hsafe; [|discriminate].
  apply andb_true_iff in Hsafe as [Hhead Htail].
  destruct Hin as [Heq|Hin]; [inversion Heq; subst; exact Hhead|eauto].
Qed.

Theorem accepted_composite_has_safe_members : forall env id su members attr co,
  bcomposite_of_def env id su members attr = OK co ->
  su = Struct /\ bmembers_layout_safe env members = true /\
  alignof_composite (bcomposite_composite_env env) (bmembers_cmembers members) <=
    align_attr attr (alignof_composite (bcomposite_composite_env env) (bmembers_cmembers members)).
Proof.
  intros env id su members attr co H.
  apply bcomposite_of_def_layout_safe in H. destruct su; [|discriminate].
  simpl in H. apply andb_true_iff in H as [Hmembers Halign].
  apply Z.leb_le in Halign. repeat split; assumption.
Qed.

Print Assumptions packet_alignment_builder_rejects_weakened_use.
Print Assumptions packet_alignment_builder_accepts_safe_strengthening.
Print Assumptions inline_alignment_guard_local.
Print Assumptions accepted_composite_has_safe_members.

(* Accepted member guards persist when later nominal definitions are added. *)
Lemma complete_remove_attributes : forall env ct,
  Ctypes.complete_type env (Ctypes.remove_attributes ct) = Ctypes.complete_type env ct.
Proof. intros env ct; destruct ct; reflexivity. Qed.

Lemma local_alignment_stable : forall env larger ty,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  (exists co, PTree.get bytes_t env = Some co) -> bcomplete_type env ty = true ->
  btype_local_alignment_safe larger ty = btype_local_alignment_safe env ty.
Proof.
  intros env larger ty Hext Hbytes Hcomplete.
  assert (Hcext : forall id co,
    PTree.get id (bcomposite_composite_env env) = Some co ->
    PTree.get id (bcomposite_composite_env larger) = Some co)
    by (apply translated_environment_extension; exact Hext).
  assert (Hct : Ctypes.complete_type (bcomposite_composite_env env) (transBeePL_type ty) = true).
  { rewrite translated_type_complete by exact Hbytes. exact Hcomplete. }
  assert (Hr : Ctypes.complete_type (bcomposite_composite_env env)
    (Ctypes.remove_attributes (transBeePL_type ty)) = true).
  { rewrite complete_remove_attributes; exact Hct. }
  unfold btype_local_alignment_safe.
  rewrite (Ctypes.alignof_stable _ _ Hcext _ Hr),
    (Ctypes.alignof_stable _ _ Hcext _ Hct). reflexivity.
Qed.

Lemma inline_alignment_stable : forall env larger,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  (exists co, PTree.get bytes_t env = Some co) ->
  forall ty, bcomplete_type env ty = true ->
  btype_inline_alignment_safe larger ty = btype_inline_alignment_safe env ty.
Proof.
  intros env larger Hext Hbytes ty. induction ty; intro Hcomplete;
    cbn [btype_inline_alignment_safe];
    rewrite local_alignment_stable with (env := env) by assumption;
    try reflexivity.
  rewrite IHty by exact Hcomplete. reflexivity.
Qed.

Fixpoint natural_object_alignment (env : bcomposite_env) (ty : type) : Z :=
  match ty with
  | Utype => 1
  | Vtype pt => alignof_ptype pt
  | Ptrtype _ => if Archi.ptr64 then 8 else 4
  | Stype id _ => match PTree.get id env with Some co => co.(BeeTypes.co_alignof) | None => 1 end
  | Atype elem _ _ => natural_object_alignment env elem
  | Ftype _ _ _ _ => 1
  | Bytes => align_chunk Mptr
  end.

Lemma power_two_le_divides : forall m n,
  two_power_nat m <= two_power_nat n -> (two_power_nat m | two_power_nat n).
Proof.
  induction m as [|m IH]; intros n Hle.
  - rewrite two_power_nat_O. apply Z.divide_1_l.
  - destruct n as [|n].
    + rewrite two_power_nat_S, two_power_nat_O in Hle.
      pose proof (two_power_nat_pos m). lia.
    + rewrite !two_power_nat_S in Hle |- *.
      destruct (IH n ltac:(lia)) as [factor Hfactor]. exists factor. nia.
Qed.

Lemma power_alignment_le_divides : forall a b,
  (exists m, a = two_power_nat m) -> (exists n, b = two_power_nat n) ->
  a <= b -> (a | b).
Proof. intros a b [m ->] [n ->] H; apply power_two_le_divides; exact H. Qed.

Lemma natural_object_alignment_power : forall env ty,
  exists n, natural_object_alignment env ty = two_power_nat n.
Proof.
  intros env ty. induction ty; simpl.
  - exists 0%nat; reflexivity.
  - destruct p as [|sz sg attr|sg attr]; try destruct sz;
      first [exists 0%nat; reflexivity|exists 1%nat; reflexivity|
             exists 2%nat; reflexivity|exists 3%nat; reflexivity].
  - destruct Archi.ptr64; [exists 3%nat|exists 2%nat]; reflexivity.
  - destruct (PTree.get i env) as [co|]; [apply co_alignof_two_p|exists 0%nat; reflexivity].
  - exact IHty.
  - exists 0%nat; reflexivity.
  - unfold Mptr. destruct Archi.ptr64; [exists 3%nat|exists 2%nat]; reflexivity.
Qed.

Lemma natural_object_alignment_size : forall env ty,
  (natural_object_alignment env ty | sizeof_type env ty).
Proof.
  intros env ty. induction ty; simpl.
  - apply Z.divide_0_r.
  - destruct p as [|sz sg attr|sg attr]; try destruct sz;
      first [apply Z.divide_refl|exists 1; reflexivity|exists 2; reflexivity].
  - destruct Archi.ptr64; apply Z.divide_refl.
  - destruct (PTree.get i env) as [co|]; [apply co_sizeof_alignof|apply Z.divide_0_r].
  - destruct IHty as [factor Hfactor]. exists (factor * Z.max 0 z). nia.
  - apply Z.divide_refl.
  - unfold Mptr. destruct Archi.ptr64; exists 2; reflexivity.
Qed.

Lemma source_complete_type_stable : forall env larger,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  forall ty, bcomplete_type env ty = true -> bcomplete_type larger ty = true.
Proof.
  intros env larger Hext ty. induction ty; simpl; intro H; try assumption; try reflexivity.
  - destruct (PTree.get i env) as [co|] eqn:Hco; [rewrite (Hext _ _ Hco); reflexivity|discriminate].
  - apply IHty; exact H.
Qed.

Lemma source_complete_members_stable : forall env larger,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  forall members, bcomplete_members env members = true -> bcomplete_members larger members = true.
Proof.
  intros env larger Hext members; induction members as [|member rest IH]; simpl; intros H; auto.
  apply andb_true_iff in H as [Hhead Htail]. apply andb_true_iff; split.
  - eapply source_complete_type_stable; eauto.
  - auto.
Qed.

Lemma members_alignment_stable : forall env larger,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  (exists co, PTree.get bytes_t env = Some co) ->
  forall members, bcomplete_members env members = true ->
  bmembers_layout_safe larger members = bmembers_layout_safe env members.
Proof.
  intros env larger Hext Hbytes members. induction members as [|member rest IH]; intros Hcomplete;
    [reflexivity|].
  simpl in Hcomplete. apply andb_true_iff in Hcomplete as [Hhead Htail].
  destruct member; simpl; [|reflexivity].
  rewrite inline_alignment_stable with (env := env) by assumption.
  rewrite IH by exact Htail. reflexivity.
Qed.

Definition source_composites_alignment_safe (env : bcomposite_env) : Prop :=
  forall id co, PTree.get id env = Some co ->
    bcomplete_members env co.(BeeTypes.co_members) = true /\
    bmembers_layout_safe env co.(BeeTypes.co_members) = true /\
    alignof_composite (bcomposite_composite_env env)
      (bmembers_cmembers co.(BeeTypes.co_members)) <= co.(BeeTypes.co_alignof).

Lemma constructed_alignment_metadata : forall env id su members attr co,
  bcomposite_of_def env id su members attr = OK co ->
  bcomplete_members env co.(BeeTypes.co_members) = true /\
  bmembers_layout_safe env co.(BeeTypes.co_members) = true /\
  alignof_composite (bcomposite_composite_env env)
    (bmembers_cmembers co.(BeeTypes.co_members)) <= co.(BeeTypes.co_alignof).
Proof.
  intros env id su members attr co Hbuild.
  pose proof (accepted_composite_has_safe_members _ _ _ _ _ _ Hbuild) as [Hsu [Hsafe Hmin]].
  apply bcomposite_of_def_layout_result in Hbuild. unfold bcomposite_layout_of_def in Hbuild.
  destruct (PTree.get id env); [discriminate|].
  destruct (bcomplete_members env members) eqn:Hcomplete; [|discriminate].
  inversion Hbuild; subst co. simpl. repeat split; assumption.
Qed.

Lemma alignment_metadata_stable : forall env larger co,
  (forall id co, PTree.get id env = Some co -> PTree.get id larger = Some co) ->
  (exists co, PTree.get bytes_t env = Some co) ->
  bcomplete_members env co.(BeeTypes.co_members) = true ->
  bmembers_layout_safe env co.(BeeTypes.co_members) = true ->
  alignof_composite (bcomposite_composite_env env)
    (bmembers_cmembers co.(BeeTypes.co_members)) <= co.(BeeTypes.co_alignof) ->
  bcomplete_members larger co.(BeeTypes.co_members) = true /\
  bmembers_layout_safe larger co.(BeeTypes.co_members) = true /\
  alignof_composite (bcomposite_composite_env larger)
    (bmembers_cmembers co.(BeeTypes.co_members)) <= co.(BeeTypes.co_alignof).
Proof.
  intros env larger co Hext Hbytes Hcomplete Hsafe Hmin.
  split; [eapply source_complete_members_stable; eauto|]. split.
  - rewrite members_alignment_stable with (env := env) by assumption. exact Hsafe.
  - rewrite Ctypes.alignof_composite_stable with (env := bcomposite_composite_env env).
    + exact Hmin.
    + apply translated_environment_extension; exact Hext.
    + rewrite translated_members_complete by exact Hbytes. exact Hcomplete.
Qed.

Lemma add_composites_alignment_safe : forall defs env final,
  add_bcomposite_definitions env defs = OK final ->
  (exists co, PTree.get bytes_t env = Some co) ->
  source_composites_alignment_safe env -> source_composites_alignment_safe final.
Proof.
  induction defs as [|[id su members attr] rest IH]; intros env final Hbuild Hbytes Hsafe.
  - simpl in Hbuild; inversion Hbuild; subst; exact Hsafe.
  - simpl in Hbuild. destruct (bcomposite_of_def env id su members attr) as [co|err] eqn:Hco;
      [|discriminate].
    assert (Hfresh : PTree.get id env = None) by (eapply constructed_composite_fresh; eauto).
    assert (Hext : forall name old, PTree.get name env = Some old ->
      PTree.get name (PTree.set id co env) = Some old).
    { intros name old Hget. rewrite PTree.gso; [exact Hget|congruence]. }
    eapply IH; [exact Hbuild| |].
    + destruct Hbytes as [bytes Hget]. exists bytes; eauto.
    + intros name found Hget. rewrite PTree.gsspec in Hget. destruct (peq name id).
      * inversion Hget; subst found.
        destruct (constructed_alignment_metadata _ _ _ _ _ _ Hco) as [Hcomplete [Hmember Hmin]].
        eapply alignment_metadata_stable; eauto.
      * destruct (Hsafe _ _ Hget) as [Hcomplete [Hmember Hmin]].
        eapply alignment_metadata_stable; eauto.
Qed.

Require Import BeePL_bytes_layout.

Lemma intrinsic_bytes_alignment_safe : source_composites_alignment_safe intrinsic_bytes_initial_env.
Proof.
  assert (Hbytes : exists co,
    intrinsic_bytes_initial_env = PTree.set bytes_t co (PTree.empty _) /\
    bcomplete_members intrinsic_bytes_initial_env co.(BeeTypes.co_members) = true /\
    bmembers_layout_safe intrinsic_bytes_initial_env co.(BeeTypes.co_members) = true /\
    alignof_composite (bcomposite_composite_env intrinsic_bytes_initial_env)
      (bmembers_cmembers co.(BeeTypes.co_members)) <= co.(BeeTypes.co_alignof)).
  { eexists. split; [reflexivity|]. repeat split; vm_compute; try reflexivity; discriminate. }
  destruct Hbytes as [bytes [Heq Hfacts]]. intros id co Hget.
  rewrite Heq, PTree.gsspec in Hget. destruct (peq id bytes_t).
  - inversion Hget; subst; exact Hfacts.
  - rewrite PTree.gempty in Hget; discriminate.
Qed.

Theorem program_composite_alignment_safe : forall p,
  source_composites_alignment_safe p.(prog_comp_env).
Proof.
  intros p. pose proof (prog_comp_env_eq p) as Hbuild.
  change (add_bcomposite_definitions intrinsic_bytes_initial_env p.(prog_types) = OK p.(prog_comp_env)) in Hbuild.
  eapply add_composites_alignment_safe; [exact Hbuild| |apply intrinsic_bytes_alignment_safe].
  destruct intrinsic_bytes_initial_layout as [co [Hget Hrest]]. eauto.
Qed.

Lemma pointer_natural_alignment : forall env ptr,
  Ctypes.alignof env (Ctypes.remove_attributes (transBeePL_ptr_type ptr)) =
    (if Archi.ptr64 then 8 else 4).
Proof.
  intros env ptr. induction ptr; simpl; auto.
  destruct b; try destruct p; reflexivity.
Qed.

Theorem guarded_natural_alignment_le : forall p ty,
  btype_inline_alignment_safe p.(prog_comp_env) ty = true ->
  natural_object_alignment p.(prog_comp_env) ty <=
    Ctypes.alignof (bcomposite_composite_env p.(prog_comp_env)) (transBeePL_type ty).
Proof.
  intros p ty. induction ty; intros Hsafe;
    pose proof (inline_alignment_guard_local _ _ Hsafe) as Hminimum.
  all: eapply Z.le_trans; [|exact Hminimum].
  - reflexivity.
  - destruct p0 as [|sz sg attr|sg attr]; try destruct sz; reflexivity.
  - cbn [natural_object_alignment transBeePL_type]. rewrite pointer_natural_alignment. reflexivity.
  - simpl. rewrite translated_composite_lookup. destruct (PTree.get i (prog_comp_env p)); reflexivity.
  - simpl. apply IHty. eapply inline_alignment_guard_array; exact Hsafe.
  - reflexivity.
  - destruct (built_bytes_layout _ _ (prog_comp_env_eq p)) as [co [Hget [_ [_ [_ Halign]]]]].
    simpl. rewrite translated_composite_lookup, Hget. simpl. rewrite Halign. reflexivity.
Qed.

Lemma plain_field_alignment_bounded : forall env members field ty,
  bmembers_layout_safe env members = true -> source_member_type field members = OK ty ->
  Ctypes.alignof (bcomposite_composite_env env) (transBeePL_type ty) <=
    alignof_composite (bcomposite_composite_env env) (bmembers_cmembers members).
Proof.
  intros env members. induction members as [|member rest IH]; intros field ty Hsafe Hfield;
    [discriminate|].
  destruct member; simpl in Hsafe; [|discriminate].
  apply andb_true_iff in Hsafe as [Hhead Htail].
  simpl in Hfield. destruct (ident_eq field i).
  - inversion Hfield; subst. simpl. apply Z.le_max_l.
  - simpl. eapply Z.le_trans; [exact (IH field ty Htail Hfield)|apply Z.le_max_r].
Qed.

Lemma safe_source_field_lookup : forall env members field ty,
  bmembers_layout_safe env members = true -> source_member_type field members = OK ty ->
  btype_inline_alignment_safe env ty = true.
Proof.
  intros env members. induction members as [|member rest IH]; intros field ty Hsafe Hfield;
    [discriminate|].
  destruct member; simpl in Hsafe; [|discriminate].
  apply andb_true_iff in Hsafe as [Hhead Htail].
  simpl in Hfield. destruct (ident_eq field i); [inversion Hfield; subst; exact Hhead|exact (IH field ty Htail Hfield)].
Qed.

Theorem program_field_natural_alignment : forall p sid attr co field ty delta,
  PTree.get sid p.(prog_comp_env) = Some co ->
  source_member_type field co.(BeeTypes.co_members) = OK ty ->
  field_offset (bcomposite_composite_env p.(prog_comp_env)) field
    (bmembers_cmembers co.(BeeTypes.co_members)) = OK (delta, Full) ->
  natural_object_alignment p.(prog_comp_env) ty <=
    natural_object_alignment p.(prog_comp_env) (Stype sid attr) /\
  (natural_object_alignment p.(prog_comp_env) ty | delta).
Proof.
  intros p sid attr co field ty delta Hget Hty Hoffset.
  destruct (program_composite_alignment_safe p sid co Hget) as [Hcomplete [Hsafe Hmin]].
  pose proof (guarded_natural_alignment_le p ty
    (safe_source_field_lookup _ _ _ _ Hsafe Hty)) as Hnatural.
  split.
  - simpl. rewrite Hget. eapply Z.le_trans; [exact Hnatural|].
    eapply Z.le_trans; [eapply plain_field_alignment_bounded; eauto|exact Hmin].
  - eapply Z.divide_trans.
    + eapply power_alignment_le_divides; [apply natural_object_alignment_power|apply Ctypes.alignof_two_p|exact Hnatural].
    + eapply Ctypes.field_offset_aligned; [exact Hoffset|].
      apply source_member_type_translation; exact Hty.
Qed.

Theorem program_object_path_alignment : forall p root offset ty,
  object_path p.(prog_comp_env) root offset ty ->
  forall divisor, (exists n, divisor = two_power_nat n) ->
    divisor <= natural_object_alignment p.(prog_comp_env) ty ->
    (divisor | offset) /\ divisor <= natural_object_alignment p.(prog_comp_env) root.
Proof.
  intros p root offset ty Hpath.
  induction Hpath as [Hsize|base sid attr co field cty ty delta Hpath IH Hget Hctype Hmember Hoffset Hdelta Hsize Hextent
    |base ty len attr index Hpath IH Hindex Hsize]; intros divisor Hpower Hbound.
  - split; [apply Z.divide_0_r|exact Hbound].
  - destruct (program_field_natural_alignment p sid attr co field ty delta Hget Hmember Hoffset)
      as [Hchild Hfield].
    destruct (IH divisor Hpower ltac:(lia)) as [Hbase Hroot].
    split; [|exact Hroot]. apply Z.divide_add_r; [exact Hbase|].
    eapply Z.divide_trans; [|exact Hfield].
    apply power_alignment_le_divides; [exact Hpower|apply natural_object_alignment_power|exact Hbound].
  - destruct (IH divisor Hpower Hbound) as [Hbase Hroot].
    split; [|exact Hroot]. apply Z.divide_add_r; [exact Hbase|].
    assert (Hstridediv : (divisor | sizeof_type (prog_comp_env p) ty)).
    { eapply Z.divide_trans; [|apply natural_object_alignment_size].
      apply power_alignment_le_divides; [exact Hpower|apply natural_object_alignment_power|exact Hbound]. }
    destruct Hstridediv as [factor Hfactor]. exists (index * factor). nia.
Qed.

Theorem program_bytes_path_aligned : forall p root delta,
  object_path p.(prog_comp_env) root delta Bytes -> (align_chunk Mptr | delta).
Proof.
  intros p root delta Hpath.
  assert (Hpower : exists n, align_chunk Mptr = two_power_nat n).
  { unfold Mptr; destruct Archi.ptr64; [exists 3%nat|exists 2%nat]; reflexivity. }
  exact (proj1 (program_object_path_alignment _ _ _ _ Hpath (align_chunk Mptr) Hpower (Z.le_refl _))).
Qed.

Print Assumptions program_composite_alignment_safe.
Print Assumptions program_object_path_alignment.
Print Assumptions program_bytes_path_aligned.
