(* Actual parameter stores and their frame properties.  No call semantics or
   legacy admitted soundness lemmas are assumed here. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_initialization_proofs BeePL_structure_proofs BeePL_array_proofs BeePL_soundness_arrays.
Import ListNotations.

Definition parameter_binding_target (vm : vmap)
    (params : list (ident * type)) (b : Values.block) : Prop :=
  exists id ty, In (id, ty) params /\ PTree.get id vm = Some (b, ty).

Lemma bind_parameters_length : forall bge vm m params values m',
  bind_variables bge vm m params values m' -> length params = length values.
Proof. intros bge vm m params values m' H; induction H; simpl; congruence. Qed.

Lemma bind_parameters_singleton_result : forall bge vm m id ty v m',
  bind_variables bge vm m [(id, ty)] [v] m' -> ty <> Utype ->
  exists b result, PTree.get id vm = Some (b, ty) /\
    assign_addr bge ty m b Ptrofs.zero Full v m' result.
Proof.
  intros bge vm m id ty v m' H Hnonunit. inversion H; subst; try contradiction.
  match goal with Hnil : bind_variables _ _ _ [] [] _ |- _ => inversion Hnil; subst end.
  eauto.
Qed.

Lemma bind_parameters_valid_blocks : forall bge vm m params values m',
  bind_variables bge vm m params values m' ->
  forall b, Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  intros bge vm m params values m' H; induction H; intros old Hvalid; auto.
  apply IHbind_variables. eapply assignment_preserves_valid_blocks; eauto.
Qed.

Lemma parameter_binding_target_tail : forall vm id ty params b,
  parameter_binding_target vm params b ->
  parameter_binding_target vm ((id, ty) :: params) b.
Proof.
  intros vm id ty params b [name [t [Hin Hget]]].
  exists name, t. split; [right; exact Hin | exact Hget].
Qed.

Lemma bind_parameters_load_frame : forall bge vm m params values m',
  bind_variables bge vm m params values m' ->
  forall b chunk ofs, ~ parameter_binding_target vm params b ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  intros bge vm m params values m' H; induction H; intros old chunk ofs Houtside.
  - reflexivity.
  - rewrite IHbind_variables.
    + eapply assignment_load_other_block; [eassumption |].
      intro Heq. subst old. apply Houtside.
      exists id, ty. split; [left; reflexivity | assumption].
    + intro Htarget. apply Houtside. eapply parameter_binding_target_tail; eauto.
  - apply IHbind_variables. intro Htarget. apply Houtside.
    eapply parameter_binding_target_tail; eauto.
Qed.

Lemma bind_parameters_cell_frame : forall bge vm m params values m',
  bind_variables bge vm m params values m' ->
  forall cenv Sigma b ofs ty chunk,
  typed_memory_cell cenv Sigma m b ofs ty chunk ->
  ~ parameter_binding_target vm params b ->
  typed_memory_cell cenv Sigma m' b ofs ty chunk.
Proof.
  intros bge vm m params values m' H; induction H;
    intros cenv Sigma old ofs cellty chunk Hcell Houtside.
  - exact Hcell.
  - apply IHbind_variables.
    + eapply assignment_typed_cell_frame; [eassumption | exact Hcell |].
      intro Heq. subst old. apply Houtside.
      exists id, ty. split; [left; reflexivity | assumption].
    + intro Htarget. apply Houtside. eapply parameter_binding_target_tail; eauto.
  - apply IHbind_variables; [exact Hcell |].
    intro Htarget. apply Houtside. eapply parameter_binding_target_tail; eauto.
Qed.

Theorem bind_parameters_layout_frame : forall bge vm m params values m' cenv Sigma layout,
  bind_variables bge vm m params values m' ->
  typed_memory_layout cenv Sigma layout m ->
  (forall b ofs ty chunk, layout b ofs ty chunk ->
    ~ parameter_binding_target vm params b) ->
  typed_memory_layout cenv Sigma layout m'.
Proof.
  intros bge vm m params values m' cenv Sigma layout Hbind Hlayout Houtside.
  intros b ofs ty chunk Hentry.
  eapply bind_parameters_cell_frame; eauto.
Qed.

Print Assumptions bind_parameters_singleton_result.
Print Assumptions bind_parameters_valid_blocks.
Print Assumptions bind_parameters_load_frame.
Print Assumptions bind_parameters_layout_frame.

(* Initialization uses the actual final parameter-store memory, not the
   freshly allocated but still uninitialized memory. *)
Theorem bind_primitive_parameter_initialized :
  forall bge vm m id pt v m' b cenv Sigma,
  bind_variables bge vm m [(id, Vtype pt)] [v] m' ->
  PTree.get id vm = Some (b, Vtype pt) ->
  typeof_value v (Vtype pt) ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Freeable ->
  typed_memory_cell cenv Sigma m' b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros bge vm m id pt v m' b cenv Sigma Hbind Hlookup Hshape Hvolatile Haccess.
  destruct (bind_parameters_singleton_result _ _ _ _ _ _ _ Hbind ltac:(discriminate))
    as [target [result [Htarget Hassign]]].
  rewrite Hlookup in Htarget. inversion Htarget; subst target.
  assert (result = v) by (inversion Hassign; reflexivity). subst result.
  pose proof (primitive_assignment_to_store bge m m' b Ptrofs.zero pt v Hshape Hassign)
    as Hstore.
  assert (Hfree : Mem.valid_access m
    (transl_bchunk_cchunk (chunk_of_ptype pt)) b (Ptrofs.unsigned Ptrofs.zero) Freeable).
  { rewrite Ptrofs.unsigned_zero. exact Haccess. }
  destruct (initialize_primitive_cell bge m b Ptrofs.zero pt v Hshape Hvolatile Hfree)
    as [written [Hwritten [_ Hcell]]].
  assert (written = m') by congruence. subst written.
  apply primitive_cell_declarative_typing. exact Hcell.
Qed.

Print Assumptions bind_primitive_parameter_initialized.

(* Distinct target blocks ensure that later parameter stores cannot overwrite
   an already initialized parameter. These are input allocation facts. *)
Definition primitive_parameter_inputs (vm : vmap) (m : Mem.mem)
    (params : list (ident * type)) (values : list value) : Prop :=
  Forall2 (fun param v => exists pt b,
    snd param = Vtype pt /\ PTree.get (fst param) vm = Some (b, Vtype pt) /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false /\
    Mem.valid_access m (transl_bchunk_cchunk (chunk_of_ptype pt)) b 0 Freeable)
    params values.

Definition parameter_targets_distinct (vm : vmap) (params : list (ident * type)) : Prop :=
  NoDup (map fst params) /\
  forall id ty id' ty' b,
    In (id, ty) params -> In (id', ty') params ->
    PTree.get id vm = Some (b, ty) -> PTree.get id' vm = Some (b, ty') -> id = id'.

Lemma assignment_valid_access_frame : forall bge ty m b ofs bf v m' result,
  assign_addr bge ty m b ofs bf v m' result ->
  forall chunk target offset permission,
  Mem.valid_access m chunk target offset permission ->
  Mem.valid_access m' chunk target offset permission.
Proof.
  intros bge ty m b ofs bf v m' result Hassign chunk target offset permission Haccess.
  inversion Hassign; subst.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_access_1; eauto end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_access_1; eauto end.
  - eapply Mem.storebytes_valid_access_1; eauto.
  - match goal with H : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_access_1; eauto end.
  - match goal with H : Mem.storev _ _ _ _ = Some _ |- _ =>
      simpl in H; eapply Mem.store_valid_access_1; eauto end.
  - eapply Mem.storebytes_valid_access_1; eauto.
Qed.

Lemma assignment_permissions_iff : forall ge ty m dst offset bf v final result b ofs k p,
  assign_addr ge ty m dst offset bf v final result ->
  (Mem.perm final b ofs k p <-> Mem.perm m b ofs k p).
Proof.
  intros ge ty m dst offset bf v final result b ofs k p Hassign.
  inversion Hassign; subst;
    try match goal with Hbit : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hbit; subst end;
    try match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ => simpl in Hstore end;
    split; intro Hperm; eauto using Mem.perm_store_1, Mem.perm_store_2,
      Mem.perm_storebytes_1, Mem.perm_storebytes_2.
Qed.

Lemma assignment_valid_blocks_iff : forall ge ty m dst offset bf v final result b,
  assign_addr ge ty m dst offset bf v final result ->
  (Mem.valid_block final b <-> Mem.valid_block m b).
Proof.
  intros ge ty m dst offset bf v final result b Hassign.
  inversion Hassign; subst;
    try match goal with Hbit : Cop.store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inversion Hbit; subst end;
    try match goal with Hstore : Mem.storev _ _ _ _ = Some _ |- _ => simpl in Hstore end;
    split; intro Hvalid; eauto using Mem.store_valid_block_1, Mem.store_valid_block_2,
      Mem.storebytes_valid_block_1, Mem.storebytes_valid_block_2.
Qed.

Lemma bind_parameters_permissions_iff : forall ge vm m params values final b ofs k p,
  bind_variables ge vm m params values final ->
  (Mem.perm final b ofs k p <-> Mem.perm m b ofs k p).
Proof.
  intros ge vm m params values final b ofs k p Hbind. induction Hbind; try tauto.
  rewrite IHHbind. eapply assignment_permissions_iff; eauto.
Qed.

Lemma bind_parameters_valid_blocks_iff : forall ge vm m params values final b,
  bind_variables ge vm m params values final ->
  (Mem.valid_block final b <-> Mem.valid_block m b).
Proof.
  intros ge vm m params values final b Hbind. induction Hbind; try tauto.
  rewrite IHHbind. eapply assignment_valid_blocks_iff; eauto.
Qed.

Lemma primitive_parameter_inputs_access : forall vm m m' params values,
  primitive_parameter_inputs vm m params values ->
  (forall chunk b ofs permission, Mem.valid_access m chunk b ofs permission ->
    Mem.valid_access m' chunk b ofs permission) ->
  primitive_parameter_inputs vm m' params values.
Proof.
  intros vm m m' params values Hinputs Haccess.
  unfold primitive_parameter_inputs in *. induction Hinputs.
  - constructor.
  - constructor; [|exact IHHinputs].
    destruct H as [pt [b [Ht [Hg [Hv [Hnv Ha]]]]]].
    exists pt, b. split; [exact Ht |]. split; [exact Hg |].
    split; [exact Hv |]. split; [exact Hnv |]. apply Haccess. exact Ha.
Qed.

Theorem bind_primitive_parameters_initialized :
  forall bge vm m params values m',
  bind_variables bge vm m params values m' ->
  primitive_parameter_inputs vm m params values ->
  parameter_targets_distinct vm params ->
  forall id pt b cenv Sigma,
  In (id, Vtype pt) params -> PTree.get id vm = Some (b, Vtype pt) ->
  typed_memory_cell cenv Sigma m' b Ptrofs.zero (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros bge vm m params values m' Hbind. induction Hbind;
    intros Hinputs Hdistinct name pt target cenv Sigma Hin Hlookup.
  - inversion Hin.
  - unfold primitive_parameter_inputs in Hinputs. inversion Hinputs; subst.
    match goal with H : exists pt b, _ |- _ =>
      destruct H as [headpt [headb [Hty [Hheadlookup [Hshape [Hvolatile Haccess]]]]]] end.
    simpl in Hty, Hheadlookup. subst ty.
    destruct Hdistinct as [Hnames Halias]. inversion Hnames; subst.
    assert (Hheadb : headb = b) by congruence. subst headb.
    assert (Htaildistinct : parameter_targets_distinct vm params).
    { split; [assumption |]. intros x xt y yt block Hx Hy Hgetx Hgety.
      eapply Halias; eauto using in_cons. }
    assert (Htailinputs : primitive_parameter_inputs vm m1 params vl).
    { eapply primitive_parameter_inputs_access; [eassumption |].
      intros chunk block offset permission Hacc.
      eapply assignment_valid_access_frame; eauto. }
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst name pt.
      assert (Htarget : target = b) by congruence. subst target.
      eapply bind_parameters_cell_frame; [exact Hbind | |].
      * eapply bind_primitive_parameter_initialized with (id := id) (v := v1).
        -- econstructor; [eassumption | eassumption | constructor].
        -- eassumption.
        -- exact Hshape.
        -- exact Hvolatile.
        -- exact Haccess.
      * intros [other [other_ty [Hother Hget]]].
        assert (other = id).
        { eapply Halias; [right; exact Hother | left; reflexivity | exact Hget | eassumption]. }
        subst other.
        match goal with Hnot : ~ In id (map fst params) |- _ =>
          apply Hnot; apply in_map with (f := @fst ident type) in Hother; exact Hother end.
    + eapply IHHbind; eauto.
  - unfold primitive_parameter_inputs in Hinputs. inversion Hinputs; subst.
    match goal with Hhead : exists pt b, _ |- _ =>
      destruct Hhead as [pt0 [block [Hty Hrest]]]; discriminate Hty end.
Qed.

Print Assumptions bind_primitive_parameters_initialized.

Theorem bind_primitive_parameters_total : forall bge vm m params values,
  primitive_parameter_inputs vm m params values ->
  exists m', bind_variables bge vm m params values m'.
Proof.
  intros bge vm m params values Hinputs.
  unfold primitive_parameter_inputs in Hinputs.
  revert m values Hinputs. induction params as [|[id ty] params IH]; intros m values Hinputs.
  - inversion Hinputs; subst. exists m. constructor.
  - inversion Hinputs as [|param value rest values_tail Hhead Htailrel]; subst.
    match goal with Hhead : exists pt b, _ |- _ =>
      destruct Hhead as [pt [b [Hty [Hlookup [Hshape [Hvolatile Haccess]]]]]] end.
    simpl in Hty, Hlookup. subst ty.
    assert (Hfree : Mem.valid_access m
      (transl_bchunk_cchunk (chunk_of_ptype pt)) b (Ptrofs.unsigned Ptrofs.zero) Freeable).
    { rewrite Ptrofs.unsigned_zero. exact Haccess. }
    destruct (initialize_primitive_cell bge m b Ptrofs.zero pt _ Hshape Hvolatile Hfree)
      as [written [Hstore [Hassign Hcell]]].
    assert (Htail : primitive_parameter_inputs vm written params values_tail).
    { eapply primitive_parameter_inputs_access; [eassumption |].
      intros chunk target offset permission Hacc.
      eapply assignment_valid_access_frame; eauto. }
    destruct (IH written values_tail Htail) as [final Hbound].
    exists final. econstructor; eauto.
Qed.

Print Assumptions bind_primitive_parameters_total.
