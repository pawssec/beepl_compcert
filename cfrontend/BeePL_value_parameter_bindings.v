(* Actual initialization for mixed unit and scalar parameter lists. Units bind
   names without touching memory; only scalar parameters contribute cells. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_call_bindings BeePL_scalar_parameters BeePL_scalar_parameter_bindings.
Require Import BeePL_call_parameters.
Import ListNotations.

Theorem bind_call_parameters_initialized : forall bge cenv Sigma L vm m params values,
  call_parameter_inputs cenv Sigma L vm m params values ->
  parameter_targets_distinct vm params ->
  exists final,
    bind_variables bge vm m params values final /\
    (forall id ty b, In (id, ty) params -> PTree.get id vm = Some (b, ty) ->
      scalar_parameter_type ty ->
      typed_memory_cell cenv Sigma final b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
      (forall loaded, deref_addr ty final b Ptrofs.zero Full loaded -> value_locations L loaded ty)).
Proof.
  intros bge cenv Sigma L vm m params values Hinputs.
  revert m values Hinputs. induction params as [|[id ty] params IH]; intros m values Hinputs Hdistinct.
  - inversion Hinputs; subst. exists m. split; [constructor|]. intros name t b Hin; contradiction.
  - inversion Hinputs; subst.
    match goal with H : exists b, _ |- _ => destruct H as [b [Hget Hkind]] end.
    simpl in Hget, Hkind.
    destruct Hdistinct as [Hnames Halias]. inversion Hnames; subst.
    assert (Htaildistinct : parameter_targets_distinct vm params).
    { split; [assumption|]. intros name t name' t' block Hin Hin' Hg Hg'.
      eapply Halias; eauto using in_cons. }
    destruct Hkind as [[Hunit Hvalue] | [Hscalar [Htyped [Hloc Hfree]]]].
    + subst ty y.
      destruct (IH m l' ltac:(assumption) Htaildistinct) as [final [Hbind Hcells]].
      exists final. split; [eapply bind_variables_unit; eauto |].
      intros name t target [Heq|Hin] Hlookup Hscalar.
      * inversion Heq; subst. exfalso. eapply scalar_parameter_not_unit; eauto.
      * eapply Hcells; eauto.
    + assert (Hfree' : Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk ty))
        b (Ptrofs.unsigned Ptrofs.zero) Freeable) by (rewrite Ptrofs.unsigned_zero; exact Hfree).
      destruct (initialize_scalar_parameter bge cenv empty_context Sigma L m b Ptrofs.zero ty _
        Hscalar Htyped Hloc Hfree') as [written [Hstore [Hassign [Hcell Hlocated]]]].
      assert (Htail : call_parameter_inputs cenv Sigma L vm written params l').
      { eapply call_parameter_inputs_access; [eassumption|].
        intros. eapply assignment_valid_access_frame; eauto. }
      destruct (IH written l' Htail Htaildistinct) as [final [Hbind Hcells]].
      exists final. split; [eapply bind_variables_cons; eauto|].
      intros name t target [Heq|Hin] Hlookup Hkind.
      * inversion Heq; subst name t. assert (target = b) by congruence. subst target.
        assert (Houtside : ~ parameter_binding_target vm params b).
        { intros [other [other_ty [Hother Hotherget]]].
          assert (Hsameid : id = other) by (eapply Halias; eauto using in_eq, in_cons).
          subst other.
          match goal with Hnotin : ~ In id (map fst params) |- _ =>
            apply Hnotin; apply in_map_iff; exists (id, other_ty); split; [reflexivity|exact Hother]
          end. }
        split.
        -- eapply bind_parameters_cell_frame; eauto.
        -- intros loaded Hread. apply Hlocated.
           eapply bind_parameters_read_backwards; eauto.
      * eapply Hcells; eauto.
Qed.

Lemma call_unit_assignment_impossible : forall bge m b v final result,
  ~ assign_addr bge Utype m b Ptrofs.zero Full v final result.
Proof. intros bge m b v final result H; inversion H; subst; discriminate. Qed.

Theorem call_parameter_binding_unique : forall bge cenv Sigma L vm m params values first,
  bind_variables bge vm m params values first ->
  call_parameter_inputs cenv Sigma L vm m params values ->
  forall second, bind_variables bge vm m params values second -> second = first.
Proof.
  intros bge cenv Sigma L vm m params values first Hbind.
  induction Hbind; intros Hinputs second Hother.
  - inversion Hother; reflexivity.
  - inversion Hinputs; subst.
    match goal with Hhead : exists b, _ |- _ => destruct Hhead as [target [Hget Hkind]] end.
    simpl in Hget, Hkind.
    destruct Hkind as [[Hunit Hvalue] | [Hscalar [Htyped [Hloc Hfree]]]].
    { subst ty. exfalso. eapply call_unit_assignment_impossible; eauto. }
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
    eapply call_parameter_inputs_access; [eassumption|].
    intros. eapply assignment_valid_access_frame; eauto.
  - inversion Hinputs; subst. inversion Hother; subst.
    + exfalso. eapply call_unit_assignment_impossible; eauto.
    + eapply IHHbind; eauto.
Qed.

Theorem bind_call_parameters_cells : forall bge cenv Sigma L vm m params values final,
  call_parameter_inputs cenv Sigma L vm m params values ->
  parameter_targets_distinct vm params ->
  bind_variables bge vm m params values final ->
  forall id ty b, In (id, ty) params -> PTree.get id vm = Some (b, ty) ->
    scalar_parameter_type ty ->
    typed_memory_cell cenv Sigma final b Ptrofs.zero ty (scalar_parameter_chunk ty) /\
    (forall loaded, deref_addr ty final b Ptrofs.zero Full loaded -> value_locations L loaded ty).
Proof.
  intros bge cenv Sigma L vm m params values final Hinputs Hdistinct Hbind.
  destruct (bind_call_parameters_initialized bge cenv Sigma L vm m params values Hinputs Hdistinct)
    as [expected [Hexpected Hcells]].
  assert (final = expected) by (eapply call_parameter_binding_unique; eauto).
  subst final. exact Hcells.
Qed.

Print Assumptions bind_call_parameters_initialized.
Print Assumptions call_parameter_binding_unique.
Print Assumptions bind_call_parameters_cells.
