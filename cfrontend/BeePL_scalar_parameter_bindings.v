(* Initialization of lists of primitive and ordinary-reference parameters. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_call_bindings BeePL_scalar_parameters.
Import ListNotations.

Definition scalar_parameter_inputs cenv Sigma L (vm : vmap) (m : Mem.mem)
    (params : list (ident * type)) (values : list value) : Prop :=
  Forall2 (fun param v => exists b,
    PTree.get (fst param) vm = Some (b, snd param) /\
    scalar_parameter_type (snd param) /\
    type_expr cenv empty_context Sigma (Val v (snd param)) nil (snd param) /\
    value_locations L v (snd param) /\
    Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk (snd param))) b 0 Freeable)
    params values.

Lemma scalar_parameter_inputs_access : forall cenv Sigma L vm m m' params values,
  scalar_parameter_inputs cenv Sigma L vm m params values ->
  (forall chunk b ofs perm, Mem.valid_access m chunk b ofs perm ->
    Mem.valid_access m' chunk b ofs perm) ->
  scalar_parameter_inputs cenv Sigma L vm m' params values.
Proof.
  intros cenv Sigma L vm m m' params values Hinputs Haccess.
  induction Hinputs; constructor; auto.
  destruct H as [b [Hget [Htype [Htyped [Hloc Hfree]]]]].
  exists b. split; [exact Hget|]. split; [exact Htype|]. split; [exact Htyped|].
  split; [exact Hloc|]. apply Haccess; exact Hfree.
Qed.

Theorem bind_scalar_parameters_total : forall bge cenv Sigma L vm m params values,
  scalar_parameter_inputs cenv Sigma L vm m params values ->
  exists final, bind_variables bge vm m params values final.
Proof.
  intros bge cenv Sigma L vm m params values Hinputs.
  revert m values Hinputs. induction params as [|[id ty] params IH]; intros m values Hinputs.
  - inversion Hinputs; subst. exists m. constructor.
  - inversion Hinputs; subst.
    match goal with H : exists b, _ |- _ =>
      destruct H as [b [Hget [Hscalar [Htyped [Hloc Hfree]]]]] end.
    simpl in Hget, Hscalar, Htyped, Hloc, Hfree.
    assert (Hfree' : Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
      b (Ptrofs.unsigned Ptrofs.zero) Freeable) by (rewrite Ptrofs.unsigned_zero; exact Hfree).
    destruct (initialize_scalar_parameter bge cenv empty_context Sigma L m b Ptrofs.zero ty _
      Hscalar Htyped Hloc Hfree') as [written [Hstore [Hassign Hrest]]].
    assert (Htail : scalar_parameter_inputs cenv Sigma L vm written params l').
    { eapply scalar_parameter_inputs_access; [eassumption|].
      intros. eapply assignment_valid_access_frame; eauto. }
    destruct (IH written l' Htail) as [final Hbind].
    exists final. econstructor; eauto.
Qed.

Lemma bind_parameters_read_backwards : forall bge vm m params values final,
  bind_variables bge vm m params values final ->
  forall b ty ofs loaded,
  ~ parameter_binding_target vm params b ->
  deref_addr ty final b ofs Full loaded -> deref_addr ty m b ofs Full loaded.
Proof.
  intros bge vm m params values final Hbind b ty ofs loaded Houtside Hread.
  inversion Hread; subst.
  - eapply deref_addr_value; eauto.
  simpl in *.
  rewrite <- (bind_parameters_load_frame _ _ _ _ _ _ Hbind b
    (transl_bchunk_cchunk chunk) (Ptrofs.unsigned ofs) Houtside).
  eassumption.
  - eapply deref_addr_bytes; [reflexivity| |eassumption|eassumption|].
    + apply (proj1 (bind_parameters_valid_blocks_iff _ _ _ _ _ _ _ Hbind)). assumption.
    + intros position Hinside.
      apply (proj1 (bind_parameters_permissions_iff _ _ _ _ _ _ _ _ _ _ Hbind)). eauto.
Qed.

Theorem bind_scalar_parameters_initialized : forall bge cenv Sigma L vm m params values,
  scalar_parameter_inputs cenv Sigma L vm m params values ->
  parameter_targets_distinct vm params ->
  exists final,
    bind_variables bge vm m params values final /\
    (forall id ty b, In (id, ty) params -> PTree.get id vm = Some (b, ty) ->
      typed_memory_cell cenv Sigma final b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
      (forall loaded, deref_addr ty final b Ptrofs.zero Full loaded -> value_locations L loaded ty)).
Proof.
  intros bge cenv Sigma L vm m params values Hinputs.
  revert m values Hinputs. induction params as [|[id ty] params IH]; intros m values Hinputs Hdistinct.
  - inversion Hinputs; subst. exists m. split; [constructor|]. intros name t b Hin; contradiction.
  - inversion Hinputs; subst.
    match goal with H : exists b, _ |- _ =>
      destruct H as [b [Hget [Hscalar [Htyped [Hloc Hfree]]]]] end.
    simpl in Hget, Hscalar, Htyped, Hloc, Hfree.
    destruct Hdistinct as [Hnames Halias]. inversion Hnames; subst.
    assert (Htaildistinct : parameter_targets_distinct vm params).
    { split; [assumption|]. intros name t name' t' block Hin Hin' Hg Hg'.
      eapply Halias; eauto using in_cons. }
    assert (Hfree' : Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
      b (Ptrofs.unsigned Ptrofs.zero) Freeable) by (rewrite Ptrofs.unsigned_zero; exact Hfree).
    destruct (initialize_scalar_parameter bge cenv empty_context Sigma L m b Ptrofs.zero ty _
      Hscalar Htyped Hloc Hfree') as [written [Hstore [Hassign [Hcell Hlocated]]]].
    assert (Htail : scalar_parameter_inputs cenv Sigma L vm written params l').
    { eapply scalar_parameter_inputs_access; [eassumption|].
      intros. eapply assignment_valid_access_frame; eauto. }
    destruct (IH written l' Htail Htaildistinct) as [final [Hbind Hcells]].
    exists final. split; [econstructor; eauto|].
    intros name t target [Heq|Hin] Hlookup.
    + inversion Heq; subst name t. assert (target = b) by congruence. subst target.
      assert (Houtside : ~ parameter_binding_target vm params b).
      { intros [other [other_ty [Hother Hotherget]]].
        assert (Hsameid : id = other) by (eapply Halias; eauto using in_eq, in_cons).
        subst other.
        match goal with Hnotin : ~ In id (map fst params) |- _ =>
          apply Hnotin; apply in_map_iff; exists (id, other_ty); split; [reflexivity|exact Hother]
        end. }
      split.
      * eapply bind_parameters_cell_frame; eauto.
      * intros loaded Hread. apply Hlocated.
        eapply bind_parameters_read_backwards; eauto.
    + eapply Hcells; eauto.
Qed.

Print Assumptions bind_scalar_parameters_total.
Print Assumptions bind_scalar_parameters_initialized.

Require Import BeePL_initialization_proofs BeePL_call_determinism.

Lemma optional_full_assignment_store : forall bge pt m b payload final result,
  assign_addr bge (Ptrtype (Otype pt)) m b Ptrofs.zero Full
    (Voption payload) final result ->
  Mem.storev Mptr m (Values.Vptr b Ptrofs.zero)
    (trans_bvalue_cvalue (Voption payload)) = Some final.
Proof.
  intros bge pt m b payload final result Hassign. inversion Hassign; subst.
  - match goal with Hdecode : trans_cvalue_bvalue ?cv = _ |- _ =>
      destruct cv; discriminate Hdecode end.
  - assumption.
Qed.

Lemma scalar_full_assignment_unique : forall bge cenv Sigma ty m b v first result second result',
  scalar_parameter_type ty ->
  type_expr cenv empty_context Sigma (Val v ty) nil ty ->
  assign_addr bge ty m b Ptrofs.zero Full v first result ->
  assign_addr bge ty m b Ptrofs.zero Full v second result' -> second = first.
Proof.
  intros bge cenv Sigma ty m b v first result second result' Hscalar Htyped Hfirst Hsecond.
  destruct Hscalar as [[[pt Hty]|[[bt [a Hty]]|[bt [a Hty]]]] Hvolatile]; subst ty.
  - eapply primitive_full_assignment_unique; eauto using declarative_value_shape.
  - inversion Htyped; subst.
    assert (result = Vloc l ofs) by (inversion Hfirst; reflexivity).
    assert (result' = Vloc l ofs) by (inversion Hsecond; reflexivity).
    subst result result'.
    assert (Hmode : access_mode_type (Ptrtype (Reftype bt a)) =
      By_value (transl_bchunk_cchunk (scalar_parameter_chunk (Ptrtype (Reftype bt a))))).
    { apply scalar_parameter_chunk_access. split; [right; left; eauto|exact Hvolatile]. }
    pose proof (full_scalar_assignment_store bge _ m b Ptrofs.zero _ (Values.Vptr l ofs) _ first
      Hmode eq_refl Hfirst) as Hstore1.
    pose proof (full_scalar_assignment_store bge _ m b Ptrofs.zero _ (Values.Vptr l ofs) _ second
      Hmode eq_refl Hsecond) as Hstore2. congruence.
  - inversion Htyped; subst.
    pose proof (optional_full_assignment_store _ _ _ _ _ _ _ Hfirst) as Hstore1.
    pose proof (optional_full_assignment_store _ _ _ _ _ _ _ Hsecond) as Hstore2.
    congruence.
Qed.

Lemma scalar_parameter_not_unit : forall ty,
  scalar_parameter_type ty -> ty <> Utype.
Proof.
  intros ty [[[pt Hty]|[[bt [a Hty]]|[bt [a Hty]]]] Hvolatile]; subst; discriminate.
Qed.

Theorem scalar_parameter_binding_unique : forall bge cenv Sigma L vm m params values first,
  bind_variables bge vm m params values first ->
  scalar_parameter_inputs cenv Sigma L vm m params values ->
  forall second, bind_variables bge vm m params values second -> second = first.
Proof.
  intros bge cenv Sigma L vm m params values first Hbind.
  induction Hbind; intros Hinputs second Hother.
  - inversion Hother; reflexivity.
  - inversion Hinputs; subst.
    match goal with Hhead : exists b, _ |- _ =>
      destruct Hhead as [target [Hget [Hscalar [Htyped [Hlocated Hfree]]]]] end.
    simpl in Hget, Hscalar, Htyped.
    inversion Hother; subst; try solve [exfalso; eapply scalar_parameter_not_unit; [exact Hscalar | reflexivity]].
    repeat match goal with
    | Hget1 : PTree.get ?id ?vm = Some (?b1, ?t),
      Hget2 : PTree.get ?id ?vm = Some (?b2, ?t) |- _ =>
      assert (b1 = b2) by congruence; first [progress subst | clear Hget2]
    end.
    match goal with
    | Hfirst : assign_addr _ _ m _ _ _ _ m1 _,
      Hsecond : assign_addr _ _ m _ _ _ _ ?other _ |- _ =>
      assert (other = m1) by (eapply scalar_full_assignment_unique; eauto);
      subst other
    end.
    apply IHHbind; [|eassumption].
    eapply scalar_parameter_inputs_access; [eassumption|].
    intros. eapply assignment_valid_access_frame; eauto.
  - inversion Hinputs; subst.
    match goal with Hhead : exists b, _ |- _ =>
      destruct Hhead as [target [Hget [Hscalar Hrest]]] end.
    exfalso. eapply scalar_parameter_not_unit; [exact Hscalar | reflexivity].
Qed.

Theorem bind_scalar_parameters_cells : forall bge cenv Sigma L vm m params values final,
  scalar_parameter_inputs cenv Sigma L vm m params values ->
  parameter_targets_distinct vm params ->
  bind_variables bge vm m params values final ->
  forall id ty b, In (id, ty) params -> PTree.get id vm = Some (b, ty) ->
    typed_memory_cell cenv Sigma final b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
    (forall loaded, deref_addr ty final b Ptrofs.zero Full loaded -> value_locations L loaded ty).
Proof.
  intros bge cenv Sigma L vm m params values final Hinputs Hdistinct Hbind.
  destruct (bind_scalar_parameters_initialized bge cenv Sigma L vm m params values Hinputs Hdistinct)
    as [expected [Hexpected Hcells]].
  assert (final = expected) by (eapply scalar_parameter_binding_unique; eauto).
  subst final. exact Hcells.
Qed.

Print Assumptions scalar_parameter_binding_unique.
Print Assumptions bind_scalar_parameters_cells.
