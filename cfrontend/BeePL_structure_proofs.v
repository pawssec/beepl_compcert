(* Resolve primitive initializer layouts from declarations before proving
   execution. This module does not assume preselected field offsets. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_initialization_proofs BeePL_layout_proofs.
Import ListNotations.

Definition plain_members (ms : members) : Prop :=
  Forall (fun m => exists name ty, m = Ctypes.Member_plain name ty) ms.

Lemma plain_field_offset_exists : forall env ms id ty,
  plain_members ms -> field_type id ms = OK ty ->
  forall pos, exists offset, field_offset_rec env id ms pos = OK (offset, Full).
Proof.
  intros env ms. induction ms as [|m ms IH]; intros id ty Hplain Htype pos;
    [discriminate |].
  inversion Hplain; subst.
  match goal with H : exists name ty, m = Ctypes.Member_plain name ty |- _ =>
    destruct H as [name [t Hm]]; subst m
  end.
  simpl in Htype |- *. destruct (ident_eq id name).
  - eexists; reflexivity.
  - eapply IH; eauto.
Qed.

Definition set_planned_offset (f : primitive_field_plan) (offset : Z) :=
  {| planned_field := planned_field f; planned_offset := offset;
     planned_type := planned_type f; planned_value := planned_value f |}.

Fixpoint resolve_primitive_fields (env : composite_env) (ms : members)
    (fs : list primitive_field_plan) : option (list primitive_field_plan) :=
  match fs with
  | [] => Some []
  | f :: rest =>
    match field_offset env (planned_field f) ms, resolve_primitive_fields env ms rest with
    | OK (offset, Full), Some resolved => Some (set_planned_offset f offset :: resolved)
    | _, _ => None
    end
  end.

Lemma resolve_primitive_fields_total : forall env ms fs,
  plain_members ms ->
  (forall f, In f fs -> exists ty, field_type (planned_field f) ms = OK ty) ->
  exists resolved, resolve_primitive_fields env ms fs = Some resolved.
Proof.
  intros env ms fs Hplain. induction fs as [|f fs IH]; intro Htypes.
  - exists []; reflexivity.
  - destruct (Htypes f (or_introl eq_refl)) as [ty Htype].
    destruct (plain_field_offset_exists env ms (planned_field f) ty Hplain Htype 0)
      as [offset Hoffset].
    destruct (IH ltac:(intros; apply Htypes; right; assumption)) as [resolved Hresolved].
    simpl. unfold field_offset. rewrite Hoffset, Hresolved. eexists; reflexivity.
Qed.

Lemma resolve_primitive_fields_spec : forall env ms fs resolved,
  resolve_primitive_fields env ms fs = Some resolved ->
  List.map planned_field resolved = List.map planned_field fs /\
  planned_expressions resolved = planned_expressions fs /\
  (forall g, In g resolved -> exists f, In f fs /\
    planned_type g = planned_type f) /\
  (forall g, In g resolved ->
    field_offset env (planned_field g) ms = OK (planned_offset g, Full)).
Proof.
  intros env ms fs. induction fs as [|f fs IH]; intros resolved Hresolve.
  - inversion Hresolve; subst. repeat split; intros; contradiction.
  - simpl in Hresolve.
    destruct (field_offset env (planned_field f) ms) as [[offset bf]|err] eqn:Hoffset;
      try discriminate.
    destruct bf; try discriminate.
    destruct (resolve_primitive_fields env ms fs) as [rest|] eqn:Hrest; try discriminate.
    inversion Hresolve; subst resolved.
    destruct (IH rest eq_refl) as [Hnames [Hexprs [Horigins Hoffsets]]].
    split; [simpl; rewrite Hnames; reflexivity |].
    split.
    + change (Val (planned_value f) (Vtype (planned_type f)) :: planned_expressions rest =
        Val (planned_value f) (Vtype (planned_type f)) :: planned_expressions fs).
      rewrite Hexprs; reflexivity.
    + split; intros g [Heq | Hin].
      * subst g. exists f. split; [left; reflexivity | reflexivity].
      * destruct (Horigins g Hin) as [original [Hmember Htype]].
        exists original. split; [right; exact Hmember | exact Htype].
      * subst g. exact Hoffset.
      * apply Hoffsets; exact Hin.
Qed.

Print Assumptions plain_field_offset_exists.
Print Assumptions resolve_primitive_fields_total.
Print Assumptions resolve_primitive_fields_spec.

Theorem resolved_primitive_structure_progress :
  forall Gamma Sigma layout p vm m sid sa pa fs ef co,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> (co.(co_sizeof) <= Ptrofs.max_unsigned)%Z ->
  Archi.align_int64 = 8%Z ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false) ->
  (forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (List.map planned_field fs) ->
  exists resolved allocated m' b,
    resolve_primitive_fields (bcomposite_composite_env p.(prog_comp_env))
      (bmembers_cmembers co.(co_members)) fs = Some resolved /\
    Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (allocated, b) /\
    ssem_expr (globalenv p) p vm m
      (Sinit sid (List.map planned_field fs) (planned_expressions fs)
        (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout p.(prog_comp_env) Sigma
      (extend_field_layout layout b Ptrofs.zero resolved) m'.
Proof.
  intros Gamma Sigma layout p vm m sid sa pa fs ef co Htyped Hmemory Hco Hstruct Hsize
    Halign Hplain Hnonvolatile Hattrs Hdistinct.
  pose proof (typed_structure_plan_facts _ _ _ _ _ _ _ _ _ Htyped Hco Hnonvolatile) as Hfacts.
  destruct (resolve_primitive_fields_total (bcomposite_composite_env p.(prog_comp_env))
    (bmembers_cmembers co.(co_members)) fs Hplain
    ltac:(intros f Hin; eexists; exact (proj2 (Hfacts f Hin)))) as [resolved Hresolve].
  destruct (resolve_primitive_fields_spec _ _ _ _ Hresolve)
    as [Hnames [Hexprs [Horigins Hoffsets]]].
  assert (Htyped' : type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field resolved) (planned_expressions resolved)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef (Ptrtype (Reftype (Bstruct sid sa) pa))).
  { rewrite Hnames, Hexprs. exact Htyped. }
  assert (Hvolatile' : forall f, In f resolved ->
    type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false).
  { intros f Hin. destruct (Horigins f Hin) as [original [Hmember Htype]].
    rewrite Htype. apply Hnonvolatile; exact Hmember. }
  assert (Hattrs' : forall f, In f resolved ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None).
  { intros f Hin. destruct (Horigins f Hin) as [original [Hmember Htype]].
    rewrite Htype. apply Hattrs; exact Hmember. }
  assert (Hdistinct' : NoDup (List.map planned_field resolved)) by (rewrite Hnames; exact Hdistinct).
  destruct (typed_primitive_structure_progress Gamma Sigma layout p vm m sid sa pa resolved ef co
    Htyped' Hmemory Hco Hstruct Hsize Halign Hoffsets Hvolatile' Hattrs' Hdistinct')
    as [allocated [m' [b [Halloc [Hstep Hmemory']]]]].
  rewrite Hnames, Hexprs in Hstep.
  exists resolved, allocated, m', b. auto.
Qed.

Print Assumptions resolved_primitive_structure_progress.

Lemma primitive_arguments_plan : forall ids es,
  length ids = length es ->
  Forall (fun e => exists v pt, e = Val v (Vtype pt)) es ->
  exists fs, List.map planned_field fs = ids /\ planned_expressions fs = es.
Proof.
  induction ids as [|id ids IH]; intros es Hlength Hvalues.
  - destruct es; [exists []; split; reflexivity | discriminate].
  - destruct es as [|e es]; [discriminate |].
    inversion Hvalues; subst.
    match goal with H : exists v pt, e = Val v (Vtype pt) |- _ =>
      destruct H as [v [pt He]]; subst e
    end.
    destruct (IH es ltac:(simpl in Hlength; congruence) ltac:(assumption))
      as [fs [Hnames Hexprs]].
    exists ({| planned_field := id; planned_offset := 0;
      planned_type := pt; planned_value := v |} :: fs).
    split; simpl; [rewrite Hnames | change
      (Val v (Vtype pt) :: planned_expressions fs = Val v (Vtype pt) :: es);
      rewrite Hexprs]; reflexivity.
Qed.

Theorem source_primitive_structure_progress :
  forall Gamma Sigma layout p vm m sid sa pa ids es ef co,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> (co.(co_sizeof) <= Ptrofs.max_unsigned)%Z ->
  Archi.align_int64 = 8%Z ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun e => exists v pt, e = Val v (Vtype pt)) es ->
  (forall e, In e es -> type_is_volatile (transBeePL_type (typeof_expr e)) = false) ->
  (forall e, In e es -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (typeof_expr e))) = None) ->
  NoDup ids ->
  exists fields allocated m' b,
    List.map planned_field fields = ids /\ planned_expressions fields = es /\
    Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (allocated, b) /\
    ssem_expr (globalenv p) p vm m
      (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout p.(prog_comp_env) Sigma
      (extend_field_layout layout b Ptrofs.zero fields) m'.
Proof.
  intros Gamma Sigma layout p vm m sid sa pa ids es ef co Htyped Hmemory Hco Hstruct Hsize
    Halign Hplain Hvalues Hnonvolatile Hattrs Hdistinct.
  destruct (typed_structure_initializer_complete _ _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [declared [_ [_ Hlength]]]].
  destruct (primitive_arguments_plan ids es Hlength Hvalues) as [fs [Hnames Hexprs]].
  assert (Hin : forall f, In f fs -> In (Val (planned_value f) (Vtype (planned_type f))) es).
  { intros f Hf. rewrite <- Hexprs. unfold planned_expressions.
    apply in_map_iff. exists f. split; [reflexivity | exact Hf]. }
  assert (Htyped' : type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef (Ptrtype (Reftype (Bstruct sid sa) pa))).
  { rewrite Hnames, Hexprs. exact Htyped. }
  assert (Hvolatile' : forall f, In f fs ->
    type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false).
  { intros f Hf. exact (Hnonvolatile _ (Hin f Hf)). }
  assert (Hattrs' : forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None).
  { intros f Hf. exact (Hattrs _ (Hin f Hf)). }
  assert (Hdistinct' : NoDup (List.map planned_field fs)) by (rewrite Hnames; exact Hdistinct).
  destruct (resolved_primitive_structure_progress Gamma Sigma layout p vm m sid sa pa fs ef co
    Htyped' Hmemory Hco Hstruct Hsize Halign Hplain Hvolatile' Hattrs' Hdistinct')
    as [fields [allocated [m' [b [Hresolved [Halloc [Hstep Hmemory']]]]]]].
  destruct (resolve_primitive_fields_spec _ _ _ _ Hresolved) as [Hnames' [Hexprs' _]].
  rewrite Hnames, Hexprs in Hstep.
  exists fields, allocated, m', b. rewrite Hnames', Hexprs', Hnames, Hexprs.
  auto.
Qed.

Print Assumptions primitive_arguments_plan.
Print Assumptions source_primitive_structure_progress.

Lemma assignment_preserves_valid_blocks : forall bge ty m addr ofs bf v m' v',
  assign_addr bge ty m addr ofs bf v m' v' ->
  forall b, Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  intros bge ty m addr ofs bf v m' v' Hassign b Hvalid.
  inversion Hassign; subst.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_block_1; [exact H | exact Hvalid]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_block_1; [exact H | exact Hvalid]
    end.
  - eapply Mem.storebytes_valid_block_1; eauto.
  - match goal with H : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_block_1; [exact H | exact Hvalid]
    end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_block_1; [exact H | exact Hvalid]
    end.
  - eapply Mem.storebytes_valid_block_1; eauto.
Qed.

Lemma field_initialization_preserves_valid_blocks : forall bge b ofs sid ids vs ts m m',
  sem_allocate_fields bge b ofs sid ids vs ts m m' ->
  forall old, Mem.valid_block m old -> Mem.valid_block m' old.
Proof.
  intros bge b ofs sid ids vs ts m m' Hinit. induction Hinit; intros old Hvalid; auto.
  apply IHHinit. eapply assignment_preserves_valid_blocks; eauto.
Qed.

Lemma initialized_structure_store_extension :
  forall bge cenv Gamma Sigma layout m allocated m' b sid sa pa ids vs ts,
  store_blocks_valid Sigma m ->
  Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa)) = (allocated, b) ->
  sem_allocate_fields bge b Ptrofs.zero sid ids vs ts allocated m' ->
  typed_memory_layout cenv Sigma layout m' ->
  let Sigma' := PTree.set b (Ptrtype (Reftype (Bstruct sid sa) pa)) Sigma in
  store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
  typed_memory_layout cenv Sigma' layout m' /\
  type_expr cenv Gamma Sigma'
    (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) nil
    (Ptrtype (Reftype (Bstruct sid sa) pa)).
Proof.
  intros bge cenv Gamma Sigma layout m allocated m' b sid sa pa ids vs ts
    Hvalid Halloc Hinit Hmemory Sigma'.
  assert (Hfresh : PTree.get b Sigma = None).
  { destruct (PTree.get b Sigma) as [oldtype|] eqn:Hget; auto.
    exfalso. eapply Mem.fresh_block_alloc; [exact Halloc |]. eapply Hvalid; eauto. }
  assert (Hextends : store_context_extends Sigma Sigma').
  { apply store_context_extends_fresh. exact Hfresh. }
  split; [exact Hextends |]. split.
  - intros old ty Hget. eapply field_initialization_preserves_valid_blocks; [exact Hinit |].
    unfold Sigma' in Hget. rewrite PTree.gsspec in Hget. destruct (Coqlib.peq old b).
    + subst old. eapply Mem.valid_new_block; eauto.
    + eapply Mem.valid_block_alloc; [exact Halloc |]. eapply Hvalid; eauto.
  - split.
    + eapply typed_memory_layout_context_extension; eauto.
    + apply ty_valloc. apply PTree.gss.
Qed.

Print Assumptions assignment_preserves_valid_blocks.
Print Assumptions field_initialization_preserves_valid_blocks.
Print Assumptions initialized_structure_store_extension.

Lemma completed_structure_initialization : forall bge p vm m sid sa pa ids es m' vm' b,
  ssem_expr bge p vm m
    (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) m' vm'
    (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) ->
  vm' = vm /\ exists allocated,
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa)) = (allocated, b) /\
    sem_allocate_fields bge b Ptrofs.zero sid ids (extract_values_exprs es)
      (typeof_exprs es) allocated m'.
Proof.
  intros bge p vm m sid sa pa ids es m' vm' b Hstep.
  inversion Hstep; subst.
  match goal with H : structure_result_type _ _ _ |- _ =>
    destruct H as [Hbad | [pa' Hptr]]; [discriminate | inversion Hptr; subst]
  end.
  split; [reflexivity |]. eexists. split; eassumption.
Qed.

Theorem source_primitive_structure_typed_progress :
  forall Gamma Sigma layout p vm m sid sa pa ids es ef co,
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  store_blocks_valid Sigma m ->
  PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> (co.(co_sizeof) <= Ptrofs.max_unsigned)%Z ->
  Archi.align_int64 = 8%Z ->
  plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun e => exists v pt, e = Val v (Vtype pt)) es ->
  (forall e, In e es -> type_is_volatile (transBeePL_type (typeof_expr e)) = false) ->
  (forall e, In e es -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (typeof_expr e))) = None) ->
  NoDup ids ->
  exists fields m' b Sigma',
    List.map planned_field fields = ids /\ planned_expressions fields = es /\
    ssem_expr (globalenv p) p vm m
      (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    typed_memory_layout p.(prog_comp_env) Sigma'
      (extend_field_layout layout b Ptrofs.zero fields) m' /\
    type_expr p.(prog_comp_env) Gamma Sigma'
      (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) nil
      (Ptrtype (Reftype (Bstruct sid sa) pa)).
Proof.
  intros Gamma Sigma layout p vm m sid sa pa ids es ef co Htyped Hmemory Hvalid Hco Hstruct Hsize
    Halign Hplain Hvalues Hnonvolatile Hattrs Hdistinct.
  destruct (source_primitive_structure_progress Gamma Sigma layout p vm m sid sa pa ids es ef co
    Htyped Hmemory Hco Hstruct Hsize Halign Hplain Hvalues Hnonvolatile Hattrs Hdistinct)
    as [fields [allocated [m' [b [Hnames [Hexprs [Halloc [Hstep Hmemory']]]]]]]].
  destruct (completed_structure_initialization _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [_ [actual [Hactual Hinit]]].
  change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (actual, b)) in Hactual.
  assert (actual = allocated) by congruence. subst actual.
  pose proof (initialized_structure_store_extension (globalenv p) p.(prog_comp_env) Gamma Sigma
    (extend_field_layout layout b Ptrofs.zero fields) m allocated m' b sid sa pa
    ids (extract_values_exprs es) (typeof_exprs es) Hvalid Halloc Hinit Hmemory') as Hpost.
  exists fields, m', b, (PTree.set b (Ptrtype (Reftype (Bstruct sid sa) pa)) Sigma).
  split; [exact Hnames |]. split; [exact Hexprs |]. split; [exact Hstep | exact Hpost].
Qed.

Print Assumptions completed_structure_initialization.
Print Assumptions source_primitive_structure_typed_progress.

Lemma primitive_assignment_to_store : forall bge m m' b ofs pt v,
  typeof_value v (Vtype pt) ->
  assign_addr bge (Vtype pt) m b ofs Full v m' v ->
  Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) m b (Ptrofs.unsigned ofs)
    (trans_bvalue_cvalue v) = Some m'.
Proof.
  intros bge m m' b ofs pt v Hshape Hassign.
  destruct pt; destruct v; simpl in Hshape; try contradiction.
  - pose proof (full_boolean_assignment_store _ _ _ _ _ _ Hassign) as Hstore.
    destruct b0; exact Hstore.
  - eapply full_scalar_assignment_store; [apply primitive_chunk_access | reflexivity | exact Hassign].
  - eapply full_scalar_assignment_store; [apply primitive_chunk_access | reflexivity | exact Hassign].
Qed.

Lemma primitive_assignment_deterministic : forall bge pt m b ofs v m1 m2,
  typeof_value v (Vtype pt) ->
  assign_addr bge (Vtype pt) m b ofs Full v m1 v ->
  assign_addr bge (Vtype pt) m b ofs Full v m2 v -> m1 = m2.
Proof.
  intros bge pt m b ofs v m1 m2 Hshape H1 H2.
  pose proof (primitive_assignment_to_store _ _ _ _ _ _ _ Hshape H1).
  pose proof (primitive_assignment_to_store _ _ _ _ _ _ _ Hshape H2). congruence.
Qed.

Lemma planned_initialization_head : forall bge b base sid f fs m m',
  field_plan_valid bge sid f ->
  sem_allocate_fields bge b base sid (List.map planned_field (f :: fs))
    (List.map planned_value (f :: fs))
    (List.map (fun f => Vtype (planned_type f)) (f :: fs)) m m' ->
  exists written,
    assign_addr bge (Vtype (planned_type f)) m b (planned_address base f) Full
      (planned_value f) written (planned_value f) /\
    sem_allocate_fields bge b base sid (List.map planned_field fs) (List.map planned_value fs)
      (List.map (fun f => Vtype (planned_type f)) fs) written m'.
Proof.
  intros bge b base sid f fs m m' [declared [Hdecl [Hoffset Hrest]]] Hinit.
  inversion Hinit; subst.
  assert (co = declared) by congruence. subst co.
  assert (Hpair : (delta, bf) = (planned_offset f, Full)) by congruence.
  inversion Hpair; subst. eexists. split; eassumption.
Qed.

Lemma planned_initialization_deterministic : forall fs bge b base sid m m1 m2,
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  sem_allocate_fields bge b base sid (List.map planned_field fs) (List.map planned_value fs)
    (List.map (fun f => Vtype (planned_type f)) fs) m m1 ->
  sem_allocate_fields bge b base sid (List.map planned_field fs) (List.map planned_value fs)
    (List.map (fun f => Vtype (planned_type f)) fs) m m2 -> m1 = m2.
Proof.
  induction fs as [|f fs IH]; intros bge b base sid m m1 m2 Hplans H1 H2.
  - inversion H1; inversion H2; subst; reflexivity.
  - pose proof (Hplans f (or_introl eq_refl)) as Hplan.
    destruct (planned_initialization_head _ _ _ _ _ _ _ _ Hplan H1) as [written1 [Hwrite1 Htail1]].
    destruct (planned_initialization_head _ _ _ _ _ _ _ _ Hplan H2) as [written2 [Hwrite2 Htail2]].
    assert (written1 = written2).
    { eapply primitive_assignment_deterministic; eauto.
      destruct Hplan as [co [_ [_ [Hshape _]]]]. exact Hshape. }
    subst written2. eapply IH; eauto.
    intros other Hin. apply Hplans. right; exact Hin.
Qed.

Print Assumptions primitive_assignment_deterministic.
Print Assumptions planned_initialization_deterministic.

Lemma planned_structure_successors :
  forall bge p vm m sid sa pa fs expected b m' vm' e',
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  ssem_expr bge p vm m
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) expected vm
    (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) ->
  ssem_expr bge p vm m
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) m' vm' e' ->
  (m' = m /\ vm' = vm /\ e' =
    Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) \/
  (m' = expected /\ vm' = vm /\ e' =
    Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))).
Proof.
  intros bge p vm m sid sa pa fs expected b m' vm' e' Hplans Hexpected Hactual.
  destruct (completed_structure_initialization _ _ _ _ _ _ _ _ _ _ _ _ Hexpected)
    as [_ [allocated [Halloc Hinit]]].
  destruct (structure_initializer_step_shape _ _ _ _ _ _ _ _ _ _ _
    (planned_expressions_values fs) Hactual) as [Hsame | Hdone]; [left; exact Hsame |].
  destruct Hdone as [sa' [actual [b' [Hresult [Halloc' [Hinit' [Hvm He]]]]]]].
  destruct Hresult as [Hbad | [pa' Hptr]]; [discriminate | inversion Hptr; subst sa' pa'].
  assert (actual = allocated /\ b' = b) by (split; congruence).
  destruct H as [Hm Hb]. subst actual b'.
  rewrite planned_expressions_extract, planned_expressions_types in Hinit, Hinit'.
  assert (m' = expected) by (eapply planned_initialization_deterministic; eauto).
  right. auto.
Qed.

Print Assumptions planned_structure_successors.

Lemma value_arguments_effect_nil : forall cenv Gamma Sigma es ef ts,
  type_exprs cenv Gamma Sigma es ef ts ->
  Forall (fun e => exists v t, e = Val v t) es -> ef = nil.
Proof.
  intros cenv Gamma Sigma es ef ts Htyped. induction Htyped; intro Hvalues; [reflexivity |].
  inversion Hvalues; subst.
  match goal with H : exists v t, e = Val v t |- _ =>
    destruct H as [v [annotation He]]; subst e
  end.
  match goal with H : type_expr _ _ _ (Val _ _) ?head_effect _ |- _ =>
    assert (Heffect : head_effect = nil) by (inversion H; reflexivity)
  end.
  rewrite Heffect. simpl. apply IHHtyped. assumption.
Qed.

Lemma planned_initializer_effect_nil : forall cenv Gamma Sigma sid sa pa fs ef,
  type_expr cenv Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) -> ef = nil.
Proof.
  intros cenv Gamma Sigma sid sa pa fs ef Htyped. inversion Htyped; subst.
  eapply value_arguments_effect_nil; [eassumption | apply planned_expressions_values].
Qed.

Theorem planned_primitive_structure_preservation :
  forall Gamma Sigma layout p vm m sid sa pa fs ef co m' vm' e',
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  store_blocks_valid Sigma m -> PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> (co.(co_sizeof) <= Ptrofs.max_unsigned)%Z ->
  Archi.align_int64 = 8%Z -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false) ->
  (forall f, In f fs ->
    attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (List.map planned_field fs) ->
  ssem_expr (globalenv p) p vm m
    (Sinit sid (List.map planned_field fs) (planned_expressions fs)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) m' vm' e' ->
  vm' = vm /\ exists Sigma' layout',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    typed_memory_layout p.(prog_comp_env) Sigma' layout' m' /\
    type_expr p.(prog_comp_env) Gamma Sigma' e' ef (Ptrtype (Reftype (Bstruct sid sa) pa)).
Proof.
  intros Gamma Sigma layout p vm m sid sa pa fs ef co m' vm' e'
    Htyped Hmemory Hvalid Hco Hstruct Hsize Halign Hplain Hvolatile Hattrs Hdistinct Hstep.
  pose proof (planned_initializer_effect_nil _ _ _ _ _ _ _ _ Htyped) as Hef. subst ef.
  destruct (resolved_primitive_structure_progress Gamma Sigma layout p vm m sid sa pa fs nil co
    Htyped Hmemory Hco Hstruct Hsize Halign Hplain Hvolatile Hattrs Hdistinct)
    as [resolved [allocated [expected [b [Hresolve [Halloc [Hexpected Hmemory']]]]]]].
  destruct (resolve_primitive_fields_spec _ _ _ _ Hresolve)
    as [Hnames [Hexprs [Horigins Hoffsets]]].
  assert (Htyped' : type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid (List.map planned_field resolved) (planned_expressions resolved)
      (Ptrtype (Reftype (Bstruct sid sa) pa))) nil (Ptrtype (Reftype (Bstruct sid sa) pa))).
  { rewrite Hnames, Hexprs. exact Htyped. }
  assert (Hvolatile' : forall f, In f resolved ->
    type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false).
  { intros f Hin. destruct (Horigins f Hin) as [original [Hmember Htype]].
    rewrite Htype. apply Hvolatile; exact Hmember. }
  pose proof (typed_structure_plan_facts _ _ _ _ _ _ _ _ _ Htyped' Hco Hvolatile') as Hfacts.
  assert (Hplans : forall f, In f resolved -> field_plan_valid (globalenv p) sid f).
  { intros f Hin. exists co. split; [exact Hco |]. split; [apply Hoffsets; exact Hin |].
    split; [exact (proj1 (Hfacts f Hin)) | apply Hvolatile'; exact Hin]. }
  rewrite <- Hnames, <- Hexprs in Hstep, Hexpected.
  destruct (planned_structure_successors _ _ _ _ _ _ _ _ _ _ _ _ _ Hplans Hexpected Hstep)
    as [[Hm [Hvm He]] | [Hm [Hvm He]]]; subst m' vm' e'.
  - split; [reflexivity |]. exists Sigma, layout.
    split; [apply store_context_extends_refl |]. split; [exact Hvalid |].
    split; [auto |]. split; assumption.
  - destruct (completed_structure_initialization _ _ _ _ _ _ _ _ _ _ _ _ Hexpected)
      as [_ [actual [Hactual Hinit]]].
    change (Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Stype sid sa)) = (actual, b)) in Hactual.
    assert (actual = allocated) by congruence. subst actual.
    pose proof (initialized_structure_store_extension (globalenv p) p.(prog_comp_env) Gamma Sigma
      (extend_field_layout layout b Ptrofs.zero resolved) m allocated expected b sid sa pa
      (List.map planned_field resolved) (extract_values_exprs (planned_expressions resolved))
      (typeof_exprs (planned_expressions resolved)) Hvalid Halloc Hinit Hmemory') as Hpost.
    destruct Hpost as [Hext [Hblocks [Hmem Hresult]]].
    split; [reflexivity |].
    exists (PTree.set b (Ptrtype (Reftype (Bstruct sid sa) pa)) Sigma),
      (extend_field_layout layout b Ptrofs.zero resolved).
    split; [exact Hext |]. split; [exact Hblocks |].
    split; [intros; apply extend_field_layout_old; assumption |]. split; assumption.
Qed.

Print Assumptions value_arguments_effect_nil.
Print Assumptions planned_primitive_structure_preservation.

Corollary source_primitive_structure_preservation :
  forall Gamma Sigma layout p vm m sid sa pa ids es ef co m' vm' e',
  type_expr p.(prog_comp_env) Gamma Sigma
    (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  typed_memory_layout p.(prog_comp_env) Sigma layout m ->
  store_blocks_valid Sigma m -> PTree.get sid p.(prog_comp_env) = Some co ->
  co.(co_su) = Struct -> (co.(co_sizeof) <= Ptrofs.max_unsigned)%Z ->
  Archi.align_int64 = 8%Z -> plain_members (bmembers_cmembers co.(co_members)) ->
  Forall (fun e => exists v pt, e = Val v (Vtype pt)) es ->
  (forall e, In e es -> type_is_volatile (transBeePL_type (typeof_expr e)) = false) ->
  (forall e, In e es -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (typeof_expr e))) = None) ->
  NoDup ids ->
  ssem_expr (globalenv p) p vm m
    (Sinit sid ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) m' vm' e' ->
  vm' = vm /\ exists Sigma' layout',
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' m' /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    typed_memory_layout p.(prog_comp_env) Sigma' layout' m' /\
    type_expr p.(prog_comp_env) Gamma Sigma' e' ef (Ptrtype (Reftype (Bstruct sid sa) pa)).
Proof.
  intros Gamma Sigma layout p vm m sid sa pa ids es ef co m' vm' e'
    Htyped Hmemory Hvalid Hco Hstruct Hsize Halign Hplain Hvalues Hvolatile Hattrs Hdistinct Hstep.
  destruct (typed_structure_initializer_complete _ _ _ _ _ _ _ _ _ _ Htyped)
    as [_ [declared [_ [_ Hlength]]]].
  destruct (primitive_arguments_plan ids es Hlength Hvalues) as [fs [Hnames Hexprs]].
  assert (Hin : forall f, In f fs -> In (Val (planned_value f) (Vtype (planned_type f))) es).
  { intros f Hf. rewrite <- Hexprs. unfold planned_expressions.
    apply in_map_iff. exists f. split; [reflexivity | exact Hf]. }
  eapply (planned_primitive_structure_preservation Gamma Sigma layout p vm m sid sa pa fs ef co
    m' vm' e'); try assumption.
  - rewrite Hnames, Hexprs. exact Htyped.
  - intros f Hf. exact (Hvolatile _ (Hin f Hf)).
  - intros f Hf. exact (Hattrs _ (Hin f Hf)).
  - rewrite Hnames. exact Hdistinct.
  - rewrite Hnames, Hexprs. exact Hstep.
Qed.

Print Assumptions source_primitive_structure_preservation.
