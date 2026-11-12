(* Structure initialization checks and operational framing. *)
Require Import List ZArith AST Integers Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory.
Import ListNotations.

Lemma typed_arguments_length : forall cenv Gamma Sigma es ef ts,
  type_exprs cenv Gamma Sigma es ef ts -> length es = length ts.
Proof. intros cenv Gamma Sigma es ef ts H; induction H; simpl; congruence. Qed.

Lemma typed_structure_initializer_complete :
  forall cenv Gamma Sigma header ids es sid sa pa ef,
  type_expr cenv Gamma Sigma
    (Sinit header ids es (Ptrtype (Reftype (Bstruct sid sa) pa))) ef
    (Ptrtype (Reftype (Bstruct sid sa) pa)) ->
  header = sid /\ exists co,
    PTree.get sid cenv = Some co /\
    ids = List.map Ctypes.name_member
      (bmembers_cmembers (List.filter (fun m => negb (member_is_padding m)) co.(co_members))) /\
    length ids = length es.
Proof.
  intros cenv Gamma Sigma header ids es sid sa pa ef Htyped.
  inversion Htyped; subst.
  match goal with H : structure_result_type _ _ _ |- _ =>
    destruct H as [Hbad | [pa' Hptr]]; [discriminate | inversion Hptr; subst]
  end.
  split; [reflexivity |].
  exists co. split; [assumption |]. split; [reflexivity |].
  match goal with
  | Hargs : type_exprs _ _ _ es _ ?ts, Hlen : length _ = length ?ts |- _ =>
    rewrite Hlen; symmetry; eapply typed_arguments_length; exact Hargs
  end.
Qed.

Lemma field_initialization_lengths : forall bge b ofs sid ids vs ts m m',
  sem_allocate_fields bge b ofs sid ids vs ts m m' ->
  length ids = length vs /\ length vs = length ts.
Proof.
  intros bge b ofs sid ids vs ts m m' Hinit.
  induction Hinit; simpl; intuition congruence.
Qed.

Lemma value_list_step_identity : forall bge p vm m es m' vm' es',
  ssem_exprs bge p vm m es m' vm' es' ->
  Forall (fun e => exists v t, e = Val v t) es ->
  m' = m /\ vm' = vm /\ es' = es.
Proof.
  intros bge p vm m es m' vm' es' Hstep. induction Hstep; intros Hvalues.
  - repeat split; reflexivity.
  - inversion Hvalues; subst.
    match goal with H : exists v t, e = Val v t |- _ => destruct H as [v [t He]]; subst e end.
    exfalso. eapply value_has_no_small_step; eauto.
  - inversion Hvalues; subst.
    destruct (IHHstep ltac:(assumption)) as [Hm [Hvm Hes]]. subst.
    repeat split; reflexivity.
Qed.

Lemma structure_initializer_step_shape :
  forall bge p vm m sid ids vs t m' vm' e',
  Forall (fun e => exists v ty, e = Val v ty) vs ->
  ssem_expr bge p vm m (Sinit sid ids vs t) m' vm' e' ->
  (m' = m /\ vm' = vm /\ e' = Sinit sid ids vs t) \/
  exists sa allocated b,
    structure_result_type sid sa t /\
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa)) = (allocated, b) /\
    sem_allocate_fields bge b Ptrofs.zero sid ids (extract_values_exprs vs)
      (typeof_exprs vs) allocated m' /\
    vm' = vm /\ e' = Val (Vloc b Ptrofs.zero) t.
Proof.
  intros bge p vm m sid ids vs t m' vm' e' Hvalues Hstep.
  inversion Hstep; subst.
  - left. match goal with H : ssem_exprs _ _ _ _ _ _ _ _ |- _ =>
      destruct (value_list_step_identity _ _ _ _ _ _ _ _ H Hvalues) as [Hm [Hvm Hes]]
    end. subst. repeat split; reflexivity.
  - right. repeat eexists; eauto.
Qed.

Print Assumptions typed_structure_initializer_complete.
Print Assumptions field_initialization_lengths.
Print Assumptions value_list_step_identity.
Print Assumptions structure_initializer_step_shape.

Lemma primitive_assignment_from_store : forall bge m m' b ofs pt v,
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) m b (Ptrofs.unsigned ofs)
    (trans_bvalue_cvalue v) = Some m' ->
  assign_addr bge (Vtype pt) m b ofs Full v m' v.
Proof.
  intros bge m m' b ofs pt v Hshape Hvolatile Hstore.
  destruct pt; destruct v; simpl in Hshape; try contradiction.
  - apply assign_addr_boolean; [reflexivity | destruct b0; exact Hstore].
  - eapply assign_addr_value; [apply primitive_chunk_access | exact Hvolatile | exact Hstore | reflexivity].
  - eapply assign_addr_value; [apply primitive_chunk_access | exact Hvolatile | exact Hstore | reflexivity].
Qed.

(* Initialization needs writable allocated space, not a pre-existing initialized
   cell. The resulting cell can be inserted into the typed layout afterwards. *)
Lemma initialize_primitive_cell : forall bge m b ofs pt v,
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b (Ptrofs.unsigned ofs) Freeable ->
  exists m',
    Mem.store (transl_bchunk_cchunk (chunk_of_ptype pt)) m b (Ptrofs.unsigned ofs)
      (trans_bvalue_cvalue v) = Some m' /\
    assign_addr bge (Vtype pt) m b ofs Full v m' v /\
    initialized_scalar_cell m' b ofs (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros bge m b ofs pt v Hshape Hvolatile Hfree.
  assert (Hwrite : Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b (Ptrofs.unsigned ofs) Writable).
  { eapply Mem.valid_access_implies; [exact Hfree | constructor]. }
  destruct (Mem.valid_access_store m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
    (Ptrofs.unsigned ofs) (trans_bvalue_cvalue v) Hwrite) as [m' Hstore].
  exists m'. split; [exact Hstore |]. split.
  - eapply primitive_assignment_from_store; eauto.
  - constructor; [apply primitive_chunk_access | exact Hvolatile | |].
    + eapply Mem.store_valid_access_1; eauto.
    + destruct (primitive_store_normalization pt v Hshape) as [stored [Hdecode Hstored]].
      eexists; exists stored. split; [eapply Mem.load_store_same; eauto |]. split; assumption.
Qed.

Print Assumptions primitive_assignment_from_store.
Print Assumptions initialize_primitive_cell.

Lemma initialize_single_primitive_field : forall bge m b ofs sid co f delta pt v,
  PTree.get sid bge.(genv_cenv) = Some co ->
  field_offset (bcomposite_composite_env bge.(genv_cenv)) f
    (bmembers_cmembers co.(co_members)) = OK (delta, Full) ->
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b
    (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) Freeable ->
  exists m', sem_allocate_fields bge b ofs sid [f] [v] [Vtype pt] m m' /\
    initialized_scalar_cell m' b (Ptrofs.add ofs (Ptrofs.repr delta)) (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros bge m b ofs sid co f delta pt v Hco Hoffset Hshape Hvolatile Hfree.
  destruct (initialize_primitive_cell bge m b (Ptrofs.add ofs (Ptrofs.repr delta)) pt v
    Hshape Hvolatile Hfree) as [m' [Hstore [Hassign Hcell]]].
  exists m'. split; [|exact Hcell].
  eapply sem_allocate_struct; [exact Hco | exact Hoffset | exact Hassign | constructor].
Qed.

Print Assumptions initialize_single_primitive_field.

Require Import BeePL_soundness_store.

Record primitive_field_plan := {
  planned_field : ident;
  planned_offset : Z;
  planned_type : primitive_type;
  planned_value : value
}.

Definition planned_address base f := Ptrofs.add base (Ptrofs.repr (planned_offset f)).
Definition planned_chunk f := chunk_of_ptype (planned_type f).
Definition planned_start base f := Ptrofs.unsigned (planned_address base f).
Definition planned_end base f :=
  (planned_start base f + size_chunk (transl_bchunk_cchunk (planned_chunk f)))%Z.

Definition field_plan_valid bge sid f : Prop :=
  exists co, PTree.get sid bge.(genv_cenv) = Some co /\
    field_offset (bcomposite_composite_env bge.(genv_cenv)) (planned_field f)
      (bmembers_cmembers co.(co_members)) = OK (planned_offset f, Full) /\
    typeof_value (planned_value f) (Vtype (planned_type f)) /\
    type_is_volatile (transBeePL_type (Vtype (planned_type f))) = false.

Fixpoint field_plans_separated base fs : Prop :=
  match fs with
  | [] => True
  | f :: fs =>
      (forall other, In other fs ->
        (planned_end base f <= planned_start base other)%Z \/
        (planned_end base other <= planned_start base f)%Z) /\
      field_plans_separated base fs
  end.

Definition field_plan_disjoint (layout : scalar_layout) b base f : Prop :=
  forall old ofs t chunk, layout old ofs t chunk ->
    old <> b \/ (planned_end base f <= Ptrofs.unsigned ofs)%Z \/
    (Ptrofs.unsigned ofs + size_chunk (transl_bchunk_cchunk chunk) <= planned_start base f)%Z.

Fixpoint extend_field_layout (layout : scalar_layout) b base fs : scalar_layout :=
  match fs with
  | [] => layout
  | f :: fs => extend_field_layout
      (extend_scalar_layout layout b (planned_address base f) (Vtype (planned_type f)) (planned_chunk f))
      b base fs
  end.

Lemma initialize_primitive_fields : forall bge sid b base fs cenv Sigma layout m,
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  (forall f, In f fs ->
    Mem.valid_access m (transl_bchunk_cchunk (planned_chunk f)) b (planned_start base f) Freeable) ->
  field_plans_separated base fs ->
  (forall f, In f fs -> field_plan_disjoint layout b base f) ->
  typed_memory_layout cenv Sigma layout m ->
  exists m',
    sem_allocate_fields bge b base sid (List.map planned_field fs) (List.map planned_value fs)
      (List.map (fun f => Vtype (planned_type f)) fs) m m' /\
    typed_memory_layout cenv Sigma (extend_field_layout layout b base fs) m'.
Proof.
  intros bge sid b base fs. induction fs as [|f fs IH];
    intros cenv Sigma layout m Hplan Haccess Hseparated Hdisjoint Hmemory.
  - exists m. split; [constructor | exact Hmemory].
  - destruct (Hplan f (or_introl eq_refl)) as [co [Hco [Hoffset [Hshape Hvolatile]]]].
    destruct (initialize_primitive_cell bge m b (planned_address base f) (planned_type f) (planned_value f)
      Hshape Hvolatile (Haccess f (or_introl eq_refl))) as [written [Hstore [Hassign Hcell]]].
    destruct Hseparated as [Hhead Htail].
    set (layout1 := extend_scalar_layout layout b (planned_address base f)
      (Vtype (planned_type f)) (planned_chunk f)).
    assert (Hmemory1 : typed_memory_layout cenv Sigma layout1 written).
    { intros old off ty ch [Hold | [Hb [Hofs [Ht Hch]]]].
      - eapply typed_memory_cell_store_disjoint; [apply Hmemory; exact Hold | exact Hstore |].
        exact (Hdisjoint f (or_introl eq_refl) old off ty ch Hold).
      - subst. apply primitive_cell_declarative_typing. exact Hcell. }
    assert (Haccess1 : forall other, In other fs ->
      Mem.valid_access written (transl_bchunk_cchunk (planned_chunk other)) b (planned_start base other) Freeable).
    { intros other Hin. eapply Mem.store_valid_access_1; [exact Hstore |].
      apply Haccess. right; exact Hin. }
    assert (Hdisjoint1 : forall other, In other fs -> field_plan_disjoint layout1 b base other).
    { intros other Hin old off ty ch [Hold | [Hb [Hofs [Ht Hch]]]].
      - exact (Hdisjoint other (or_intror Hin) old off ty ch Hold).
      - subst old off ty ch. pose proof (Hhead other Hin) as Hsep.
        unfold planned_end, planned_start in *. tauto. }
    destruct (IH cenv Sigma layout1 written ltac:(intros; apply Hplan; right; assumption)
      Haccess1 Htail Hdisjoint1 Hmemory1) as [m' [Hrest Hmemory']].
    exists m'. split; [|exact Hmemory'].
    simpl. eapply sem_allocate_struct; [exact Hco | exact Hoffset | exact Hassign | exact Hrest].
Qed.

Print Assumptions initialize_primitive_fields.

Lemma extend_field_layout_old : forall fs layout b base old ofs t chunk,
  layout old ofs t chunk -> extend_field_layout layout b base fs old ofs t chunk.
Proof.
  induction fs as [|f fs IH]; intros layout b base old ofs t chunk Hentry; simpl.
  - exact Hentry.
  - apply IH. left; exact Hentry.
Qed.

Lemma extend_field_layout_member : forall fs layout b base f,
  In f fs -> extend_field_layout layout b base fs b (planned_address base f)
    (Vtype (planned_type f)) (planned_chunk f).
Proof.
  induction fs as [|head fs IH]; intros layout b base f Hin; [contradiction |].
  destruct Hin as [Heq | Hin]; simpl.
  - subst head. apply extend_field_layout_old. right; repeat split; reflexivity.
  - apply IH. exact Hin.
Qed.

Definition planned_expressions fs :=
  List.map (fun f => Val (planned_value f) (Vtype (planned_type f))) fs.

Lemma planned_expressions_values : forall fs,
  Forall (fun e => exists v t, e = Val v t) (planned_expressions fs).
Proof.
  intros fs. induction fs; simpl; constructor; auto.
  eexists; eexists; reflexivity.
Qed.

Lemma planned_expressions_extract : forall fs,
  extract_values_exprs (planned_expressions fs) = List.map planned_value fs.
Proof. intros fs; induction fs; simpl; congruence. Qed.

Lemma planned_expressions_types : forall fs,
  typeof_exprs (planned_expressions fs) = List.map (fun f => Vtype (planned_type f)) fs.
Proof. intros fs; induction fs; simpl; congruence. Qed.

Lemma typed_planned_arguments : forall fs cenv Gamma Sigma ef ts,
  type_exprs cenv Gamma Sigma (planned_expressions fs) ef ts ->
  ts = List.map (fun f => Vtype (planned_type f)) fs /\
  forall f, In f fs -> typeof_value (planned_value f) (Vtype (planned_type f)).
Proof.
  induction fs as [|f fs IH]; intros cenv Gamma Sigma ef ts Htyped.
  - inversion Htyped; subst. split; [reflexivity | intros; contradiction].
  - inversion Htyped; subst.
    match goal with
    | Hhead : type_expr _ _ _ (Val _ _) _ _,
      Htail : type_exprs _ _ _ (planned_expressions fs) _ _ |- _ =>
      pose proof (type_rel_typeof _ _ _ _ _ _ Hhead) as Htype;
      pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hhead) as Hvalue;
      destruct (IH _ _ _ _ _ Htail) as [Htypes Hvalues]
    end.
    simpl in Htype. subst. split; [reflexivity |].
    intros other [Heq | Hin]; [subst; assumption | apply Hvalues; exact Hin].
Qed.

Print Assumptions typed_planned_arguments.

Lemma primitive_structure_initialization_progress :
  forall bge cenv Sigma layout p vm m sid sa pa fs,
  typed_memory_layout cenv Sigma layout m ->
  (forall f, In f fs -> field_plan_valid bge sid f) ->
  field_plans_separated Ptrofs.zero fs ->
  (forall f, In f fs ->
    (0 <= planned_start Ptrofs.zero f)%Z /\
    (planned_end Ptrofs.zero f <= sizeof_type bge.(genv_cenv) (Stype sid sa))%Z /\
    (align_chunk (transl_bchunk_cchunk (planned_chunk f)) | planned_start Ptrofs.zero f)%Z) ->
  exists allocated m' b,
    Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa)) = (allocated, b) /\
    ssem_expr bge p vm m
      (Sinit sid (List.map planned_field fs) (planned_expressions fs)
        (Ptrtype (Reftype (Bstruct sid sa) pa)))
      m' vm (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) pa))) /\
    typed_memory_layout cenv Sigma (extend_field_layout layout b Ptrofs.zero fs) m'.
Proof.
  intros bge cenv Sigma layout p vm m sid sa pa fs Hmemory Hplan Hseparated Hbounds.
  destruct (Mem.alloc m 0 (sizeof_type bge.(genv_cenv) (Stype sid sa))) as [allocated b] eqn:Halloc.
  assert (Hallocated : typed_memory_layout cenv Sigma layout allocated).
  { intros old off ty ch Hentry. eapply typed_memory_cell_alloc_frame; eauto. }
  assert (Haccess : forall f, In f fs ->
    Mem.valid_access allocated (transl_bchunk_cchunk (planned_chunk f)) b (planned_start Ptrofs.zero f) Freeable).
  { intros f Hin. destruct (Hbounds f Hin) as [Hlo [Hhi Halign]].
    eapply Mem.valid_access_alloc_same; eauto. }
  assert (Hdisjoint : forall f, In f fs -> field_plan_disjoint layout b Ptrofs.zero f).
  { intros f Hin old off ty ch Hentry. left. intro Heq. subst old.
    eapply Mem.fresh_block_alloc; [exact Halloc |].
    eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure; eauto. }
  destruct (initialize_primitive_fields bge sid b Ptrofs.zero fs cenv Sigma layout allocated
    Hplan Haccess Hseparated Hdisjoint Hallocated) as [m' [Hinit Hmemory']].
  exists allocated, m', b. split; [reflexivity |]. split; [|exact Hmemory'].
  eapply ssem_sinit2 with (allocated := allocated) (loc := b) (sa := sa).
  - right. exists pa. reflexivity.
  - apply planned_expressions_values.
  - exact Halloc.
  - rewrite planned_expressions_extract, planned_expressions_types. exact Hinit.
Qed.

Print Assumptions extend_field_layout_member.
Print Assumptions primitive_structure_initialization_progress.

Lemma initialized_planned_field_read :
  forall bge cenv Gamma Sigma layout p vm m sid sa fs b f,
  In f fs -> field_plan_valid bge sid f ->
  typed_memory_layout cenv Sigma (extend_field_layout layout b Ptrofs.zero fs) m ->
  exists v,
    ssem_expr bge p vm m
      (Sfield (Val (Vloc b Ptrofs.zero) (Ptrtype (Reftype (Bstruct sid sa) noattr)))
        (planned_field f) (Vtype (planned_type f)))
      m vm (Val v (Vtype (planned_type f))) /\
    type_expr cenv Gamma Sigma (Val v (Vtype (planned_type f))) nil (Vtype (planned_type f)).
Proof.
  intros bge cenv Gamma Sigma layout p vm m sid sa fs b f Hin Hplan Hmemory.
  destruct Hplan as [co [Hco [Hoffset Hrest]]].
  pose proof (extend_field_layout_member fs layout b Ptrofs.zero f Hin) as Hentry.
  destruct (typed_memory_cell_read cenv Gamma Sigma m b (planned_address Ptrofs.zero f)
    (Vtype (planned_type f)) (planned_chunk f) (Hmemory _ _ _ _ Hentry))
    as [v [Hread Htyped]].
  exists v. split; [eapply ssem_sfield2; eauto | exact Htyped].
Qed.

Print Assumptions initialized_planned_field_read.
