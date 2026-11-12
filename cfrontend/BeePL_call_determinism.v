(* Determinism of call preparation, not of the entire expression relation. *)
Require Import List ZArith AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_structure_proofs BeePL_call_bindings BeePL_strict_progress.
Import ListNotations.
Local Open Scope Z_scope.

Theorem parameter_allocation_runtime_unique :
  forall bge Sigma vm m params callee allocated Sigma',
  alloc_variables bge Sigma vm m params callee allocated Sigma' ->
  forall OtherSigma other_callee other_allocated OtherSigma',
  alloc_variables bge OtherSigma vm m params other_callee other_allocated OtherSigma' ->
  other_callee = callee /\ other_allocated = allocated.
Proof.
  intros bge Sigma vm m params callee allocated Sigma' Halloc.
  induction Halloc; intros OtherSigma other_callee other_allocated OtherSigma' Hother.
  - inversion Hother; subst; auto.
  - inversion Hother; subst.
    unfold balloc in *.
    destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty)) as [first fresh] eqn:Hmem.
    repeat match goal with H : (_, _, _) = (_, _, _) |- _ => inversion H; clear H; subst end.
    eapply IHHalloc; eauto.
Qed.

Lemma primitive_full_assignment_unique : forall bge pt m b v first result second result',
  typeof_value v (Vtype pt) ->
  assign_addr bge (Vtype pt) m b Ptrofs.zero Full v first result ->
  assign_addr bge (Vtype pt) m b Ptrofs.zero Full v second result' ->
  second = first.
Proof.
  intros bge pt m b v first result second result' Hshape Hfirst Hsecond.
  assert (result = v) by (inversion Hfirst; reflexivity).
  assert (result' = v) by (inversion Hsecond; reflexivity). subst result result'.
  eapply primitive_assignment_deterministic; eauto.
Qed.

Theorem primitive_parameter_binding_unique : forall bge vm m params values first,
  bind_variables bge vm m params values first ->
  primitive_parameter_inputs vm m params values ->
  forall second, bind_variables bge vm m params values second -> second = first.
Proof.
  intros bge vm m params values first Hbind. induction Hbind;
    intros Hinputs second Hother.
  - inversion Hother; reflexivity.
  - unfold primitive_parameter_inputs in Hinputs. inversion Hinputs; subst.
    match goal with Hhead : exists pt b, _ |- _ =>
      destruct Hhead as [pt [target [Hty [Hget [Hshape [Hvolatile Haccess]]]]]] end.
    simpl in Hty, Hget. subst ty.
    inversion Hother; subst.
    repeat match goal with
    | Hget1 : PTree.get ?id ?vm = Some (?b1, ?t),
      Hget2 : PTree.get ?id ?vm = Some (?b2, ?t) |- _ =>
      assert (b1 = b2) by congruence; first [progress subst | clear Hget2]
    end.
    match goal with
    | Hfirst : assign_addr _ _ m _ _ _ _ m1 _,
      Hsecond : assign_addr _ _ m _ _ _ _ ?other _ |- _ =>
      assert (other = m1) by (eapply primitive_full_assignment_unique; eauto);
      subst other
    end.
    apply IHHbind; [|eassumption].
    eapply primitive_parameter_inputs_access; [eassumption |].
    intros chunk block offset permission Hacc.
    eapply assignment_valid_access_frame; eauto.
  - unfold primitive_parameter_inputs in Hinputs. inversion Hinputs; subst.
    match goal with Hhead : exists pt b, _ |- _ =>
      destruct Hhead as [pt0 [block [Hty Hrest]]]; discriminate Hty end.
Qed.

Print Assumptions parameter_allocation_runtime_unique.
Print Assumptions primitive_parameter_binding_unique.

Theorem primitive_call_preparation_unique :
  forall bge Sigma m params values callee allocated Sigma' final,
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  primitive_parameter_inputs callee allocated params values ->
  bind_variables bge callee allocated params values final ->
  forall OtherSigma other_callee other_allocated OtherSigma' other_final,
  alloc_variables bge OtherSigma empty_vmap m params
    other_callee other_allocated OtherSigma' ->
  bind_variables bge other_callee other_allocated params values other_final ->
  other_callee = callee /\ other_allocated = allocated /\ other_final = final.
Proof.
  intros bge Sigma m params values callee allocated Sigma' final Halloc Hinputs Hbind
    OtherSigma other_callee other_allocated OtherSigma' other_final Hother Hotherbind.
  destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ Halloc
    _ _ _ _ Hother) as [Hmap Hmemory]. subst other_callee other_allocated.
  split; [reflexivity |]. split; [reflexivity |].
  eapply primitive_parameter_binding_unique; eauto.
Qed.

Print Assumptions primitive_call_preparation_unique.

Require Import Coqlib Globalenvs BeePL_parameter_allocations BeePL_initialization_proofs.
Require Import BeePL_soundness_memory.

Lemma actual_primitive_allocation_inputs :
  forall bge Sigma m params values callee allocated Sigma',
  alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params values ->
  primitive_parameter_inputs callee allocated params values.
Proof.
  intros bge Sigma m params values callee allocated Sigma' Halloc Hnames Hshapes.
  destruct (allocate_primitive_parameters bge Sigma m params values Hnames Hshapes)
    as [other [memory [store [Hother [Hinputs Hrest]]]]].
  destruct (parameter_allocation_runtime_unique _ _ _ _ _ _ _ _ Halloc
    _ _ _ _ Hother) as [Hmap Hmem]. subst. exact Hinputs.
Qed.

Lemma call_parameter_names_nodup : forall (params : list (ident * type)),
  list_norepet (seq.unzip1 params) -> NoDup (map fst params).
Proof.
  induction params as [|[id ty] params IH]; simpl; intros H; inversion H; subst;
    constructor; auto.
Qed.

Lemma parameter_shapes_exclude_functions : forall (R : (ident * type) -> value -> Prop) params values,
  Forall2 R params values ->
  (forall param v, R param v -> is_funtype (snd param) = false) ->
  ~ has_function_parameter params.
Proof.
  intros R params values Hshapes Hkind.
  assert (Htypes : Forall (fun param => is_funtype (snd param) = false) params).
  { induction Hshapes; constructor; eauto. }
  intros [id [args [effects [result [variadic Hin]]]]].
  rewrite Forall_forall in Htypes. specialize (Htypes _ Hin). discriminate Htypes.
Qed.

(* Evaluated data-only calls have an actual entry successor. Function-valued
   parameters use their separate immutable-code preparation rule. *)
Lemma evaluated_application_step_cases :
  forall (bge : genv) p caller m b ofs annotation es ret m' caller' e',
  Forall (fun e => exists v ty, e = Val v ty) es ->
  (forall fn, Genv.find_funct bge (trans_bvalue_cvalue (Vloc b ofs)) = Some (Internal fn) ->
    ~ has_function_parameter (fn_args fn)) ->
  ssem_expr bge p caller m (App (Val (Vloc b ofs) annotation) es ret) m' caller' e' ->
  caller' = caller /\
   exists fn callee Sigma Sigma' allocated,
     Genv.find_funct bge (trans_bvalue_cvalue (Vloc b ofs)) = Some (Internal fn) /\
     alloc_variables bge Sigma empty_vmap m fn.(fn_args) callee allocated Sigma' /\
     bind_variables bge callee allocated fn.(fn_args) (extract_values_exprs es) m' /\
     list_norepet (seq.unzip1 fn.(fn_args)) /\
     e' = CallFrame callee fn.(fn_body) ret.
Proof.
  intros bge p caller m b ofs annotation es ret m' caller' e' Hvalues Hdata Hstep.
  pose proof (all_value_arguments_is_values es Hvalues) as Hready.
  inversion Hstep; subst.
  - exfalso. eapply value_has_no_small_step; eauto.
  - congruence.
  - split; [reflexivity |]. do 5 eexists. repeat split; eauto.
  - exfalso. eapply Hdata; eauto.
Qed.

Theorem evaluated_application_entry_unique :
  forall (bge : genv) p caller m b annotation es ret fn callee body initialized,
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    fn.(fn_args) (extract_values_exprs es) ->
  ssem_expr bge p caller m (App (Val (Vloc b Ptrofs.zero) annotation) es ret)
    initialized caller (CallFrame callee body ret) ->
  forall m' caller' e',
  ssem_expr bge p caller m (App (Val (Vloc b Ptrofs.zero) annotation) es ret)
    m' caller' e' ->
  caller' = caller /\
  ((m' = m /\ e' = App (Val (Vloc b Ptrofs.zero) annotation) es ret) \/
   (m' = initialized /\ e' = CallFrame callee body ret)).
Proof.
  intros bge p caller m b annotation es ret fn callee body initialized
    Hfn Hvalues Hshapes Hentry m' caller' e' Hstep.
  assert (Hnofun : ~ has_function_parameter (fn_args fn)).
  { eapply parameter_shapes_exclude_functions; [exact Hshapes |].
    intros [id ty] value [pt [Hty Hrest]]. simpl in Hty |- *. subst ty. reflexivity. }
  assert (Hdata : forall target,
    Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal target) ->
    ~ has_function_parameter (fn_args target)).
  { intros target Hfind. assert (target = fn) by congruence. subst target. exact Hnofun. }
  destruct (evaluated_application_step_cases _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hdata Hentry)
    as [_ [firstfn [firstcallee [Sigma [Sigma' [allocated
      [Hfirstfn [Halloc [Hbind [Hnames Hframe]]]]]]]]]].
  assert (firstfn = fn) by congruence. subst firstfn.
  inversion Hframe; subst firstcallee body.
  destruct (evaluated_application_step_cases _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hdata Hstep)
    as [Hcaller [otherfn [othercallee [OtherSigma [OtherSigma' [otherallocated
      [Hotherfn [Hotheralloc [Hotherbind [Hothernames Hotherframe]]]]]]]]]].
  split; [exact Hcaller |]. right.
  assert (otherfn = fn) by congruence. subst otherfn.
  assert (Hinputs : primitive_parameter_inputs callee allocated (fn_args fn) (extract_values_exprs es)).
  { eapply actual_primitive_allocation_inputs; eauto using call_parameter_names_nodup. }
  destruct (primitive_call_preparation_unique _ _ _ _ _ _ _ _ _ Halloc Hinputs Hbind
    _ _ _ _ _ Hotheralloc Hotherbind) as [Hmap [Hmem Hfinal]].
  subst othercallee. split; assumption.

Qed.

Print Assumptions evaluated_application_entry_unique.
