(* Scalar assignment establishes caller closure preservation from the prestate.
   This is not yet confinement for aggregate copies or whole checked calls. *)
Require Import List ZArith AST Maps Memory Memdata Values Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_escape_store BeePL_call_bindings BeePL_compiler_frame_release.

Lemma no_new_pointer_fragments_retains_memory : forall keep f before after,
  retained_memory keep f before ->
  pointer_fragments_preserved before after ->
  (forall b ofs, Mem.perm after b ofs Cur Readable ->
                 Mem.perm before b ofs Cur Readable) ->
  retained_memory keep f after.
Proof.
  intros keep f before after Hclosed Hfragments Hpermissions
    b target delta ofs Hmap Hkeep Hread.
  unfold retained_memval.
  destruct (ZMap.get ofs (PMap.get b (Mem.mem_contents after)))
    as [|byte|v quantity index] eqn:E; simpl; auto.
  destruct v; simpl; auto.
  specialize (Hfragments _ _ _ _ _ _ E).
  specialize (Hclosed b target delta ofs Hmap Hkeep (Hpermissions _ _ Hread)).
  unfold retained_memval in Hclosed. rewrite Hfragments in Hclosed. exact Hclosed.
Qed.

Theorem typed_scalar_assignment_retains_memory :
  forall ge cenv Gamma Sigma keep f pt m b ofs v final result,
  retained_memory keep f m ->
  type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
  assign_addr ge (Vtype pt) m b ofs Full v final result ->
  retained_memory keep f final.
Proof.
  intros ge cenv Gamma Sigma keep f pt m b ofs v final result
    Hclosed Htyped Hassign.
  eapply no_new_pointer_fragments_retains_memory; [exact Hclosed| |].
  - eapply typed_primitive_assignment_no_new_pointer_fragments; eauto.
  - intros block offset Hread.
    eapply (proj1 (assignment_permissions_iff _ _ _ _ _ _ _ _ _ _ _ _ _ Hassign)); exact Hread.
Qed.

(* Every element of this execution relation is an actual checked scalar store;
   there is no final-state closure premise. *)
Inductive typed_scalar_assignments (ge : genv) (cenv : bcomposite_env)
    (Gamma : ty_context) (Sigma : store_context) : mem -> mem -> Prop :=
| typed_scalar_assignments_nil : forall m, typed_scalar_assignments ge cenv Gamma Sigma m m
| typed_scalar_assignments_cons : forall m middle final pt b ofs v result,
    type_expr cenv Gamma Sigma (Val v (Vtype pt)) nil (Vtype pt) ->
    assign_addr ge (Vtype pt) m b ofs Full v middle result ->
    typed_scalar_assignments ge cenv Gamma Sigma middle final ->
    typed_scalar_assignments ge cenv Gamma Sigma m final.

Theorem typed_scalar_assignments_retain_memory : forall ge cenv Gamma Sigma
    keep f before after,
  typed_scalar_assignments ge cenv Gamma Sigma before after ->
  retained_memory keep f before -> retained_memory keep f after.
Proof.
  intros ge cenv Gamma Sigma keep f before after Hsteps.
  induction Hsteps; intros Hclosed; auto.
  apply IHHsteps. eapply typed_scalar_assignment_retains_memory; eauto.
Qed.

Print Assumptions typed_scalar_assignment_retains_memory.
Print Assumptions typed_scalar_assignments_retain_memory.
