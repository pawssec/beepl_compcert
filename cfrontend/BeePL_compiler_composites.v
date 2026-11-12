(* Layout correspondence for actual successful builders.  The target may
   contain additional generated composites; no arbitrary-environment equality
   or source/C scalar-size equivalence is asserted. *)
Require Import List Maps AST Coqlib Errors Ctypes Classical_Prop.
Require Import BeeTypes BeePL_layout_proofs BeePL_Csyntax BeePL_Bytes_Struct BeePL_Check_Reserved_Struct BeePL_Wrapper_Pass.
Require Import BeePL_representation_check.
Import ListNotations.

(* Use Coq's theorem from classical logic, not CompCert's standalone
   proof-irrelevance axiom, when identifying proof fields in layout records. *)
Lemma compiler_composite_eq :
  forall su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1
         su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2,
  su1=su2 -> m1=m2 -> a1=a2 -> sz1=sz2 -> al1=al2 -> r1=r2 ->
  Build_composite su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1 =
  Build_composite su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2.
Proof.
  intros; subst.
  assert (pos1=pos2) by apply Classical_Prop.proof_irrelevance.
  assert (al2p1=al2p2) by apply Classical_Prop.proof_irrelevance.
  assert (szal1=szal2) by apply Classical_Prop.proof_irrelevance.
  subst; reflexivity.
Qed.

Lemma compiler_composite_of_def_eq : forall env id co,
  composite_consistent env co -> env!id=None ->
  composite_of_def env id (Ctypes.co_su co) (Ctypes.co_members co)
    (Ctypes.co_attr co)=OK co.
Proof.
  intros env id co [A B C D] Hfresh. unfold composite_of_def.
  rewrite Hfresh,A. destruct co; simpl in *.
  f_equal. apply compiler_composite_eq; auto. rewrite C,B; auto.
Qed.

Lemma compiler_composite_of_def_stable : forall env target,
  (forall id co, env!id=Some co -> target!id=Some co) ->
  forall id su members attr co,
  target!id=None -> composite_of_def env id su members attr=OK co ->
  composite_of_def target id su members attr=OK co.
Proof.
  intros env target Hext id su members attr co Hfresh Hbuild.
  unfold composite_of_def in Hbuild.
  destruct (env!id) eqn:E; try discriminate.
  destruct (complete_members env members) eqn:C; try discriminate.
  transitivity (composite_of_def target id (Ctypes.co_su co)
    (Ctypes.co_members co) (Ctypes.co_attr co)).
  - inversion Hbuild; reflexivity.
  - apply compiler_composite_of_def_eq; auto.
    eapply composite_consistent_stable; [exact Hext|].
    inversion Hbuild; constructor; auto.
Qed.

Definition translated_composites_included (source:bcomposite_env)
    (target:composite_env) : Prop :=
  forall id co, source!id=Some co ->
    target!id=Some(bcomposite_ccomposite co).

Lemma source_composite_conversion : forall env id su members attr co,
  bcomposite_of_def env id su members attr=OK co ->
  complete_members (bcomposite_composite_env env)
    (bmembers_cmembers members)=true ->
  composite_of_def (bcomposite_composite_env env) id su
    (bmembers_cmembers members) attr=OK(bcomposite_ccomposite co).
Proof.
  intros env id su members attr co Hbuild Hcomplete.
  pose proof (constructed_composite_consistent _ _ _ _ _ _ Hbuild Hcomplete) as Hconsistent.
  pose proof (constructed_composite_fresh _ _ _ _ _ _ Hbuild) as Hfresh.
  assert (Htarget : (bcomposite_composite_env env)!id=None).
  { rewrite translated_composite_lookup,Hfresh. reflexivity. }
  apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  rewrite Hfresh in Hbuild.
  destruct (bcomplete_members env members); try discriminate.
  inversion Hbuild; subst co.
  pose proof (compiler_composite_of_def_eq _ _ _ Hconsistent Htarget) as E.
  cbn in E. exact E.
Qed.

Lemma source_composite_conversion_with_bytes : forall env id su members attr co,
  (exists bytes, env!bytes_t=Some bytes) ->
  bcomposite_of_def env id su members attr=OK co ->
  composite_of_def (bcomposite_composite_env env) id su
    (bmembers_cmembers members) attr=OK(bcomposite_ccomposite co).
Proof.
  intros env id su members attr co Hbytes Hbuild.
  apply source_composite_conversion; auto.
  rewrite translated_members_complete by exact Hbytes.
  apply bcomposite_of_def_layout_result in Hbuild.
  unfold bcomposite_layout_of_def in Hbuild.
  destruct (env!id); try discriminate.
  destruct (bcomplete_members env members); congruence.
Qed.

Lemma converted_additions_preserve_source_layout : forall defs source final target targetfinal,
  (exists bytes, source!bytes_t=Some bytes) ->
  translated_composites_included source target ->
  add_bcomposite_definitions source defs=OK final ->
  add_composite_definitions target
    (map bcomposite_ccomposite_definition defs)=OK targetfinal ->
  translated_composites_included final targetfinal.
Proof.
  induction defs as [|[id su members attr] rest IH];
    intros source final target targetfinal Hbytes Hincl Hsource Htarget.
  - simpl in *. inversion Hsource; inversion Htarget; subst. exact Hincl.
  - simpl in Hsource,Htarget.
    destruct (bcomposite_of_def source id su members attr) as [co|err] eqn:Hco;
      try discriminate.
    destruct (composite_of_def target id su (bmembers_cmembers members) attr)
      as [cc|err] eqn:Hcc; try discriminate.
    assert (Hfresh : target!id=None).
    { unfold composite_of_def in Hcc. destruct (target!id); congruence. }
    assert (Hsame : cc=bcomposite_ccomposite co).
    { pose proof (source_composite_conversion_with_bytes _ _ _ _ _ _ Hbytes Hco) as Hconverted.
      assert (Hstable : composite_of_def target id su (bmembers_cmembers members) attr=
        OK(bcomposite_ccomposite co)).
      { eapply compiler_composite_of_def_stable with (env := bcomposite_composite_env source); [|exact Hfresh|exact Hconverted].
        intros key value Hget. rewrite translated_composite_lookup in Hget.
        destruct (source!key) as [bco|] eqn:E; simpl in Hget; try discriminate.
        inversion Hget; subst. apply Hincl; exact E. }
      congruence. }
    subst cc. eapply IH with (source := PTree.set id co source)
      (target := PTree.set id (bcomposite_ccomposite co) target);
      [| |exact Hsource|exact Htarget].
    + destruct Hbytes as [bytes E]. exists bytes.
      rewrite PTree.gso; auto.
      pose proof (constructed_composite_fresh _ _ _ _ _ _ Hco). congruence.
    + intros key value Hget. rewrite PTree.gsspec in Hget |- *.
      destruct (peq key id); [inversion Hget; reflexivity|]. apply Hincl; exact Hget.
Qed.

Lemma target_additions_preserve_source_layout : forall source target defs final,
  translated_composites_included source target ->
  add_composite_definitions target defs=OK final ->
  translated_composites_included source final.
Proof.
  intros source target defs final Hincl Hbuild id co Hget.
  eapply add_composite_definitions_incr; eauto.
Qed.

(* Both builders receive the intrinsic Bytes declaration first here.  The
   actual compiler's generated prefix must separately be shown to contain this
   seed before this theorem is applied to its user-definition suffix. *)
Theorem built_source_target_composites_correspond : forall defs source target,
  build_bcomposite_env defs=OK source ->
  build_composite_env
    (map bcomposite_ccomposite_definition
      (bytes_bcomposite_definition :: defs))=OK target ->
  translated_composites_included source target.
Proof.
  intros defs source target Hsource Htarget.
  unfold build_bcomposite_env in Hsource.
  unfold build_composite_env in Htarget.
  cbn [List.map add_bcomposite_definitions add_composite_definitions
    bytes_bcomposite_definition bcomposite_ccomposite_definition] in Hsource,Htarget.
  eapply converted_additions_preserve_source_layout;
    [| |exact Hsource|exact Htarget].
  - eexists. apply PTree.gss.
  - intros id co Hget. rewrite PTree.gsspec in Hget |- *.
    destruct (peq id bytes_t).
    + inversion Hget; subst. reflexivity.
    + rewrite PTree.gempty in Hget. discriminate.
Qed.

Print Assumptions source_composite_conversion.
Print Assumptions converted_additions_preserve_source_layout.
Print Assumptions target_additions_preserve_source_layout.
Print Assumptions built_source_target_composites_correspond.

Lemma collected_composites_are_bytes : forall types,
  Forall (fun c => c=bcomposite_ccomposite_definition bytes_bcomposite_definition)
    (get_bcs_from_types types).
Proof.
  induction types as [|ty rest IH]; [constructor|].
  destruct ty; simpl; auto.
Qed.

Lemma global_collected_composites_are_bytes : forall defs,
  Forall (fun c => c=bcomposite_ccomposite_definition bytes_bcomposite_definition)
    (get_bcs_from_globdefs_aux defs).
Proof.
  induction defs as [|gd rest IH]; simpl; [constructor|].
  apply Forall_app; split; auto.
  destruct gd as [fd|gv]; simpl; [destruct fd|]; try constructor.
  apply collected_composites_are_bytes.
Qed.

Lemma deduplicated_bytes_seed : forall cs,
  Forall (fun c => c=bcomposite_ccomposite_definition bytes_bcomposite_definition) cs ->
  remove_duplicate_composites
    (bcomposite_ccomposite_definition bytes_bcomposite_definition :: cs)=
    [bcomposite_ccomposite_definition bytes_bcomposite_definition].
Proof.
  intros cs H; induction H as [|c cs E H IH]; [reflexivity|].
  subst c. change
    ((if mem_composite_id bytes_t
       (remove_duplicate_composites
         (bcomposite_ccomposite_definition bytes_bcomposite_definition :: cs))
     then remove_duplicate_composites
       (bcomposite_ccomposite_definition bytes_bcomposite_definition :: cs)
     else bcomposite_ccomposite_definition bytes_bcomposite_definition ::
       remove_duplicate_composites
         (bcomposite_ccomposite_definition bytes_bcomposite_definition :: cs)) =
       [bcomposite_ccomposite_definition bytes_bcomposite_definition]).
  rewrite IH. reflexivity.
Qed.

Lemma compiler_bytes_prefix : forall defs,
  get_bcs_from_globdefs defs=
    [bcomposite_ccomposite_definition bytes_bcomposite_definition].
Proof.
  intros. apply deduplicated_bytes_seed. apply global_collected_composites_are_bytes.
Qed.

Theorem built_source_with_target_extras : forall defs source target prefix extras,
  build_bcomposite_env defs=OK source ->
  build_composite_env
    (prefix ++ bcomposite_ccomposite_definition bytes_bcomposite_definition ::
       extras ++ map bcomposite_ccomposite_definition defs)=OK target ->
  translated_composites_included source target.
Proof.
  intros defs source target prefix extras Hsource Htarget.
  unfold build_composite_env in Htarget.
  apply add_composite_definitions_append in Htarget as [before [Hprefix Htarget]].
  cbn [add_composite_definitions bcomposite_ccomposite_definition
    bytes_bcomposite_definition] in Htarget.
  destruct (composite_of_def before bytes_t Struct
    (bmembers_cmembers
      [Member_plain bytes_start (Ptrtype(Reftype(Bprim(Tint I8 Unsigned noattr)) noattr));
       Member_plain bytes_end (Ptrtype(Reftype(Bprim(Tint I8 Unsigned noattr)) noattr))]) noattr)
    as [bytes|err] eqn:Hbytes; try discriminate.
  apply add_composite_definitions_append in Htarget as [middle [Hextras Htarget]].
  unfold build_bcomposite_env in Hsource.
  cbn [add_bcomposite_definitions bytes_bcomposite_definition] in Hsource.
  eapply converted_additions_preserve_source_layout;
    [| |exact Hsource|exact Htarget].
  - eexists; apply PTree.gss.
  - eapply target_additions_preserve_source_layout; [|exact Hextras].
    intros id co Hget. rewrite PTree.gsspec in Hget.
    destruct (peq id bytes_t) as [->|Hneq].
    + inversion Hget; subst co. rewrite PTree.gss.
      unfold composite_of_def in Hbytes.
      destruct (before!bytes_t); try discriminate.
      inversion Hbytes; subst bytes.
      f_equal. apply compiler_composite_eq; reflexivity.
    + rewrite PTree.gempty in Hget. discriminate.
Qed.

Lemma made_program_composite_definitions : forall cs defs publics main cp,
  @Ctypes.make_program Csyntax.function cs defs publics main=OK cp ->
  Ctypes.prog_types cp=cs.
Proof.
  intros cs defs publics main cp. unfold Ctypes.make_program.
  generalize (eq_refl (Ctypes.build_composite_env cs)).
  generalize (Ctypes.build_composite_env cs) at 1 3.
  intros r E H. destruct r; inversion H; reflexivity.
Qed.

Lemma made_program_composite_build : forall cs defs publics main cp,
  @Ctypes.make_program Csyntax.function cs defs publics main=OK cp ->
  Ctypes.build_composite_env cs=OK(Ctypes.prog_comp_env cp).
Proof.
  intros cs defs publics main cp H.
  rewrite <- (made_program_composite_definitions _ _ _ _ _ H).
  apply Ctypes.prog_comp_env_eq.
Qed.

Theorem successful_compiler_composite_layout : forall p cp names sections,
  BeePL_compcert p=OK(cp,names,sections) ->
  translated_composites_included (BeePL.prog_comp_env p)
    (Ctypes.prog_comp_env cp).
Proof.
  intros p cp names sections H. unfold BeePL_compcert in H.
  destruct(check_struct_from_program p) eqn:Echeck; simpl in H; try discriminate.
  destruct(check_compiler_representation p) eqn:Erepresentation; simpl in H; try discriminate.
  destruct(BeePL_escape_check.check_reference_escapes p) eqn:Eescape; simpl in H; try discriminate.
  destruct(transBeePL_globdefs_globdefs _ _ _ _) as [[[[outs ns] extra] ctx]|msg] eqn:Edefs;
    simpl in H; try discriminate.
  destruct(Ctypes.make_program _ _ _ _) as [made|msg] eqn:Emade;
    simpl in H; try discriminate.
  inversion H; subst.
  apply made_program_composite_build in Emade.
  rewrite compiler_bytes_prefix in Emade.
  match type of Emade with
  | context [if ?test then _ else _] => destruct test eqn:Ectx
  end.
  - eapply built_source_with_target_extras with (prefix := [xdp_md_ccomposite]);
      [apply BeePL.prog_comp_env_eq|exact Emade].
  - eapply built_source_with_target_extras with (prefix := []);
      [apply BeePL.prog_comp_env_eq|exact Emade].
Qed.

Corollary compiler_composite_lookup_preserved : forall p cp names sections id co,
  BeePL_compcert p=OK(cp,names,sections) ->
  (BeePL.prog_comp_env p)!id=Some co ->
  (Ctypes.prog_comp_env cp)!id=Some(bcomposite_ccomposite co).
Proof.
  intros. eapply successful_compiler_composite_layout; eauto.
Qed.

Print Assumptions successful_compiler_composite_layout.
Print Assumptions compiler_composite_lookup_preserved.

Lemma included_composites_extend_translated_environment : forall source target,
  translated_composites_included source target ->
  forall id co, (bcomposite_composite_env source)!id=Some co -> target!id=Some co.
Proof.
  intros source target Hincl id co Hget.
  rewrite translated_composite_lookup in Hget.
  destruct (source!id) as [sourceco|] eqn:E; simpl in Hget; try discriminate.
  inversion Hget; subst. apply Hincl; exact E.
Qed.

(* These are C representation sizes in the two related environments. They
   intentionally do not identify BeePL sizeof_type with C sizeof: unit arrays
   have a separate source/C representation obligation. *)
Theorem compiler_complete_type_representation_layout : forall p cp names sections ty,
  BeePL_compcert p=OK(cp,names,sections) ->
  bcomplete_type (BeePL.prog_comp_env p) ty=true ->
  Ctypes.sizeof (Ctypes.prog_comp_env cp) (transBeePL_type ty)=
    Ctypes.sizeof (bcomposite_composite_env (BeePL.prog_comp_env p)) (transBeePL_type ty) /\
  Ctypes.alignof (Ctypes.prog_comp_env cp) (transBeePL_type ty)=
    Ctypes.alignof (bcomposite_composite_env (BeePL.prog_comp_env p)) (transBeePL_type ty).
Proof.
  intros p cp names sections ty Hcompile Hcomplete.
  pose proof (included_composites_extend_translated_environment _ _
    (successful_compiler_composite_layout _ _ _ _ Hcompile)) as Hext.
  assert (Hc : complete_type (bcomposite_composite_env (BeePL.prog_comp_env p))
    (transBeePL_type ty)=true).
  { rewrite translated_type_complete; auto.
    eapply built_source_bytes_present. apply BeePL.prog_comp_env_eq. }
  split; [eapply Ctypes.sizeof_stable|eapply Ctypes.alignof_stable]; eauto.
Qed.

Print Assumptions compiler_complete_type_representation_layout.
