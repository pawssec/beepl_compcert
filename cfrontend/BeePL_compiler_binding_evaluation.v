(* Scoped Bind operational bridge. Source Bind substitutes a value: it does not
   allocate a source block. C stores its value in a fresh, private local. Child
   evaluation premises are the induction interface, not execution assumptions
   for the generated parent expression. *)
Require Import List String ZArith Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Csyntax Csem Cstrategy Cop SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_Csyntax BeePL_compiler_bindings.
Require Import BeePL_compiler_expression_types BeePL_compiler_decomposition.
Import ListNotations.
Local Open Scope Z_scope.

Definition binding_prefix (selected : option ident) (ty : BeeTypes.type) rhs :=
  match selected with
  | Some target => Eassign (Evar target (transBeePL_type ty)) rhs (transBeePL_type ty)
  | None => rhs
  end.

Lemma translated_binding_shape :
  forall x ty rhs body result locals bc generated locals' bc' g g' inc
    selected slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2,
  transBeePL_expr_expr (Bind x ty rhs body result) locals bc g =
    Res (generated,locals',bc') g' inc ->
  fresh_compiler_binding x ty locals bc g = Res ((selected,slots),scope) g0 i0 ->
  transBeePL_expr_expr rhs slots bc g0 = Res (crhs,rhs_locals,rhs_bc) g1 i1 ->
  transBeePL_expr_expr body rhs_locals scope g1 = Res (cbody,body_locals,body_bc) g2 i2 ->
  generated = Ecomma (binding_prefix selected ty crhs) cbody (transBeePL_type result) /\
  locals' = body_locals /\ bc' = bc.
Proof.
  intros x ty rhs body result locals bc generated locals' bc' g g' inc
    selected slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2
    Hwhole Hfresh Hrhs Hbody.
  cbn [transBeePL_expr_expr] in Hwhole.
  unfold SimplExpr.bind2, SimplExpr.bind in Hwhole.
  rewrite Hfresh in Hwhole; cbn beta iota zeta delta [fst snd] in Hwhole.
  rewrite Hrhs in Hwhole; cbn beta iota zeta delta [fst snd] in Hwhole.
  rewrite Hbody in Hwhole; cbn [ret fst snd] in Hwhole.
  inversion Hwhole; subst; repeat split; reflexivity.
Qed.

Lemma local_assignment_after_child :
  forall ge env before rhs_memory assigned target slot ty rhs child_trace value normalized chunk,
  env!target = Some (slot,ty) ->
  Cstrategy.eval_expression ge env before rhs child_trace rhs_memory value ->
  Cop.sem_cast value (Csyntax.typeof rhs) ty rhs_memory = Some normalized ->
  access_mode ty = By_value chunk -> type_is_volatile ty = false ->
  Mem.store chunk rhs_memory slot 0 normalized = Some assigned ->
  Cstrategy.eval_expr ge env before RV (Eassign (Evar target ty) rhs ty)
    child_trace assigned (Eval normalized ty).
Proof.
  intros ge env before rhs_memory assigned target slot ty rhs child_trace value normalized chunk
    Hlocal Hrhs Hcast Hmode Hvolatile Hstore.
  inversion Hrhs as [e m a trace m' reduced v Heval Hsimple]; subst.
  replace child_trace with (E0 ** child_trace ** E0) by (rewrite E0_left, E0_right; reflexivity).
  eapply Cstrategy.eval_assign with (m1:=before)(m2:=rhs_memory)
    (b:=slot)(ofs:=Ptrofs.zero)(bf:=Full)(v:=value)(v1:=normalized).
  - constructor.
  - exact Heval.
  - apply Cstrategy.esl_var_local; exact Hlocal.
  - exact Hsimple.
  - exact Hcast.
  - eapply Csem.assign_loc_value; eauto.
  - reflexivity.
Qed.

Lemma comma_from_child_evaluations :
  forall ge env before middle final first body result first_trace body_trace first_value value,
  Cstrategy.eval_expression ge env before first first_trace middle first_value ->
  Cstrategy.eval_expression ge env middle body body_trace final value ->
  result = Csyntax.typeof body ->
  Cstrategy.eval_expression ge env before (Ecomma first body result)
    (first_trace ** body_trace) final value.
Proof.
  intros ge env before middle final first body result first_trace body_trace first_value value
    Hfirst Hbody Htype.
  inversion Hfirst as [e m a t m' reduced1 v Hstep1 Hsimple1]; subst.
  inversion Hbody as [e m a t m' reduced2 v Hstep2 Hsimple2]; subst.
  eapply Cstrategy.eval_expression_intro; [eapply Cstrategy.eval_comma; eauto|exact Hsimple2].
Qed.

(* The selected slot and all child terms come from the actual successful
   translation. Assignment uses the real pointee width and emits no trace. *)
Theorem compiled_scalar_binding_from_children :
  forall ge env x ty rhs body result locals bc generated locals' bc' g g' inc
    target slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2
    before rhs_memory assigned final rhs_trace body_trace value normalized answer slot chunk,
  transBeePL_expr_expr (Bind x ty rhs body result) locals bc g =
    Res (generated,locals',bc') g' inc ->
  fresh_compiler_binding x ty locals bc g = Res ((Some target,slots),scope) g0 i0 ->
  transBeePL_expr_expr rhs slots bc g0 = Res (crhs,rhs_locals,rhs_bc) g1 i1 ->
  transBeePL_expr_expr body rhs_locals scope g1 = Res (cbody,body_locals,body_bc) g2 i2 ->
  result = typeof_expr body ->
  env!target = Some (slot,transBeePL_type ty) ->
  Cstrategy.eval_expression ge env before crhs rhs_trace rhs_memory value ->
  Cop.sem_cast value (Csyntax.typeof crhs) (transBeePL_type ty) rhs_memory = Some normalized ->
  access_mode (transBeePL_type ty) = By_value chunk ->
  type_is_volatile (transBeePL_type ty) = false ->
  Mem.store chunk rhs_memory slot 0 normalized = Some assigned ->
  Cstrategy.eval_expression ge env assigned cbody body_trace final answer ->
  Cstrategy.eval_expression ge env before generated (rhs_trace ** body_trace) final answer.
Proof.
  intros ge env x ty rhs body result locals bc generated locals' bc' g g' inc
    target slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2
    before rhs_memory assigned final rhs_trace body_trace value normalized answer slot chunk
    Hwhole Hfresh Hrhs Hbody Htype Hlocal Heval Hcast Hmode Hvolatile Hstore Hbodyeval.
  destruct (translated_binding_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hwhole Hfresh Hrhs Hbody) as [Hshape _]. rewrite Hshape.
  eapply comma_from_child_evaluations; [|exact Hbodyeval|].
  - eapply Cstrategy.eval_expression_intro.
    + cbn [binding_prefix]. eapply local_assignment_after_child; eauto.
    + constructor.
  - subst result. eapply compilation_preserve_type_checked; exact Hbody.
Qed.

Theorem compiled_no_slot_binding_from_children :
  forall ge env x ty rhs body result locals bc generated locals' bc' g g' inc
    slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2
    before middle final rhs_trace body_trace value answer,
  transBeePL_expr_expr (Bind x ty rhs body result) locals bc g = Res (generated,locals',bc') g' inc ->
  fresh_compiler_binding x ty locals bc g = Res ((None,slots),scope) g0 i0 ->
  transBeePL_expr_expr rhs slots bc g0 = Res (crhs,rhs_locals,rhs_bc) g1 i1 ->
  transBeePL_expr_expr body rhs_locals scope g1 = Res (cbody,body_locals,body_bc) g2 i2 ->
  result = typeof_expr body ->
  Cstrategy.eval_expression ge env before crhs rhs_trace middle value ->
  Cstrategy.eval_expression ge env middle cbody body_trace final answer ->
  Cstrategy.eval_expression ge env before generated (rhs_trace ** body_trace) final answer.
Proof.
  intros ge env x ty rhs body result locals bc generated locals' bc' g g' inc
    slots scope g0 i0 crhs rhs_locals rhs_bc g1 i1 cbody body_locals body_bc g2 i2
    before middle final rhs_trace body_trace value answer
    Hwhole Hfresh Hrhs Hbody Htype Heval Hbodyeval.
  destruct (translated_binding_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hwhole Hfresh Hrhs Hbody) as [Hshape _]. rewrite Hshape.
  eapply comma_from_child_evaluations; [exact Heval|exact Hbodyeval|].
  subst result. eapply compilation_preserve_type_checked; exact Hbody.
Qed.

(* A source Bind head does not allocate or mutate source memory. A private C
   local store can therefore keep precisely the SAME injection. No source
   allocation is fabricated to justify the extra target local. *)
Theorem private_binding_store_preserves_injection :
  forall f source target chunk slot normalized,
  Mem.inject f source target ->
  (forall b delta, f b <> Some (slot,delta)) ->
  Mem.valid_access target chunk slot 0 Writable ->
  exists assigned, Mem.store chunk target slot 0 normalized = Some assigned /\
    Mem.inject f source assigned.
Proof.
  intros f source target chunk slot normalized Hinject Hprivate Haccess.
  destruct (Mem.valid_access_store _ _ _ _ normalized Haccess) as [assigned Hstore].
  exists assigned; split; [exact Hstore|].
  eapply Mem.store_outside_inject; [exact Hinject| |exact Hstore].
  intros b delta offset Hmap Hread Hrange. exact (Hprivate b delta Hmap).
Qed.

Local Opaque fresh_ident max_fresh.
Lemma actual_nonunit_binding_scope : forall x ty locals bc selected slots scope g g' inc,
  ty <> Utype ->
  fresh_compiler_binding x ty locals bc g = Res ((selected,slots),scope) g' inc ->
  exists target name,
    selected = Some target /\ slots = (target,ty,name)::locals /\
    scope = with_compiler_bindings bc
      (push_compiler_binding (lexical_bindings bc) x (Binding_slot target)) /\
    compiler_bound_storage (lexical_bindings scope) x = Some target /\
    (forall other, other <> x ->
      (lexical_bindings scope)!other = (lexical_bindings bc)!other).
Proof.
  intros x ty locals bc selected slots scope g g' inc Hnonunit Hfresh.
  destruct ty; try solve [exfalso; apply Hnonunit; reflexivity];
    cbn [fresh_compiler_binding] in Hfresh;
    unfold SimplExpr.bind2, SimplExpr.bind in Hfresh;
    match type of Hfresh with
    | context [fresh_ident ?names ?fuel ?gen] =>
      destruct (fresh_ident names fuel gen) as [err|[target name] gg ii] eqn:Hid
    end; try discriminate;
    cbn [ret] in Hfresh; inversion Hfresh; subst selected slots scope;
    exists target,name; repeat split; try reflexivity;
    try apply compiler_fresh_slot_access;
    intros other Hneq; apply compiler_binding_other; exact Hneq.
Qed.

(* This is the concrete source head/target-prefix interface. The source takes
   its real substitution step with unchanged memory; the target initializes
   its private local. The body simulation then continues in the scoped mapping
   proved above. Cast stability is stated explicitly for this head lemma. *)
Theorem evaluated_binding_head_private_slot :
  forall bge p vm ge env f source target x ty value body substituted
    local slot chunk target_value,
  SubstE x (Val value ty) body substituted ->
  Mem.inject f source target ->
  (forall b delta, f b <> Some (slot,delta)) ->
  env!local = Some (slot,transBeePL_type ty) ->
  access_mode (transBeePL_type ty) = By_value chunk ->
  type_is_volatile (transBeePL_type ty) = false ->
  Val.inject f (trans_bvalue_cvalue value) target_value ->
  Cop.sem_cast target_value (transBeePL_type ty)
    (transBeePL_type ty) target = Some target_value ->
  Mem.valid_access target chunk slot 0 Writable ->
  exists assigned,
    ssem_expr bge p vm source (Bind x ty (Val value ty) body (typeof_expr body))
      source vm substituted /\
    Mem.inject f source assigned /\
    Val.inject f (trans_bvalue_cvalue value) target_value /\
    Cstrategy.eval_expression ge env target
      (binding_prefix (Some local) ty (Eval target_value (transBeePL_type ty)))
      E0 assigned target_value.
Proof.
  intros bge p vm ge env f source target x ty value body substituted local slot chunk target_value
    Hsubst Hinject Hprivate Hlocal Hmode Hvolatile Hvalue Hcast Haccess.
  destruct (private_binding_store_preserves_injection f source target chunk slot
    target_value Hinject Hprivate Haccess) as [assigned [Hstore Hinject']].
  exists assigned; split; [eapply ssem_bind2; exact Hsubst|].
  split; [exact Hinject'|]. split; [exact Hvalue|].
  eapply Cstrategy.eval_expression_intro.
  - cbn [binding_prefix]. eapply local_assignment_after_child; eauto.
    eapply Cstrategy.eval_expression_intro; constructor.
  - constructor.
Qed.

Print Assumptions actual_nonunit_binding_scope.
Print Assumptions evaluated_binding_head_private_slot.
Print Assumptions compiled_scalar_binding_from_children.
Print Assumptions compiled_no_slot_binding_from_children.
Print Assumptions private_binding_store_preserves_injection.
