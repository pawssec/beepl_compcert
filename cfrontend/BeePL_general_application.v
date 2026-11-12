(* Evaluated internal applications use the full shared program invariant. *)
Require Import List Bool Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_type_equality BeePL_substitution_proofs BeePL_initializer_slot.
Require Import BeePL_program_runtime BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_packet_bindings.
Require Import BeePL_general_call_entry BeePL_application_configuration.
Import ListNotations.

Lemma evaluated_application_function_components : forall env Gamma Sigma vf tf es result ef,
  type_expr env Gamma Sigma(App(Val vf tf) es result) ef result ->
  Forall(fun e=>exists v annotation,e=Val v annotation) es ->
  exists args effects variadic,tf=Ftype args effects result variadic /\ef=effects /\
    type_expr env Gamma Sigma(Val vf tf) [] tf /\type_exprs env Gamma Sigma es [] args.
Proof.
  intros env Gamma Sigma vf tf es result ef Htyped Hvalues.
  inversion Htyped;subst.
  match goal with Hvalue:type_expr _ _ _ (Val vf tf) _ ?te|-_=>
    pose proof(type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
    simpl in Hannotation;subst te end.
  match goal with Hcompat:context[orb(eq_type tf _)(eq_type tf _)]|-_=>
    change((eq_type tf(Ptrtype(Fptype ts efs result v)) ||eq_type tf(Ftype ts efs result v))=true) in Hcompat;
    apply orb_true_iff in Hcompat;destruct Hcompat as [Hptr|Hfun] end.
  - apply eq_type_sound in Hptr;subst tf;exfalso;eapply direct_function_pointer_value_uninhabited;eauto.
  - apply eq_type_sound in Hfun;subst tf.
    match goal with Hvalue:type_expr _ _ _ (Val vf _) _ _|-_=>
      pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hnil;subst end.
    match goal with Hargs:type_exprs _ _ _ es _ _|-_=>
      pose proof(evaluated_arguments_effect_nil _ _ _ _ _ _ Hargs Hvalues) as Hnil;subst end.
    exists ts,efs,v;simpl;rewrite app_nil_r;repeat split;assumption||reflexivity.
Qed.

Theorem general_application_entry_configuration : forall p globals Gamma Sigma vm m objects cells packets vf tf args result ef,
  program_runtime_configuration p globals Gamma Sigma vm m objects cells packets(App(Val vf tf) args result) ef result ->
  Forall(fun e=>exists v annotation,e=Val v annotation) args ->
  exists final callee fn Sigma' objects' cells' packets',
    ssem_expr(globalenv p) p vm m(App(Val vf tf) args result) final vm(CallFrame callee(fn_body fn) result) /\
    initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    program_runtime_configuration p globals Gamma Sigma' vm final objects' cells' packets'
      (CallFrame callee(fn_body fn) result) ef result.
Proof.
  intros p globals Gamma Sigma vm m objects cells packets vf tf args result ef [Hprogram [Hconfig Hcoherent]] Hvalues.
  destruct Hconfig as [Hheap Htyped Hlocations Hframes].
  destruct(evaluated_application_function_components _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [types [effects [variadic [Htf [Hef [Hfunction Hargs]]]]]]. subst tf ef.
  destruct(typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Hfunction) as [Hnil [Hannotation [b Hv]]]. subst vf.
  simpl in Hlocations;destruct Hlocations as [HcodeLocation HargLocations].
  assert(Hcall:internal_code_locations(globalenv p) b Ptrofs.zero(Ftype types effects result variadic)).
  { destruct HcodeLocation as [[Hcall|[[Hkind Hobj]|[basic [attr [Hbad Hobj]]]]]|[Hbytes Hp]];
      [exact Hcall|discriminate Hkind|discriminate Hbad|discriminate Hbytes]. }
  destruct Hcall as [Hz [types' [effects' [result' [variadic' [fn [Hsame [Hfind Hsignature]]]]]]]].
  inversion Hsame;subst types' effects' result' variadic'.
  pose proof Hsignature as Hcomponents;unfold type_of_function in Hcomponents;inversion Hcomponents;subst types effects result variadic.
  destruct(general_internal_call_entry p globals Gamma Sigma vm m objects cells packets b fn args
    Hprogram Hfind Hargs Hvalues HargLocations Hheap Hcoherent)
    as [callee [final [Sigma' [objects' [cells' [packets' [Hstep [Hevol Hfinal]]]]]]]].
  exists final,callee,fn,Sigma',objects',cells',packets';split.
  - rewrite <-Hsignature;exact Hstep.
  - split;[exact Hevol|]. constructor;[eapply program_runtime_invariant_evolve;[exact Hprogram|exact Hevol]|exact Hfinal].
Qed.

Theorem general_application_progress : forall p globals Gamma Sigma vm m objects cells packets vf tf args result ef,
  program_runtime_configuration p globals Gamma Sigma vm m objects cells packets(App(Val vf tf) args result) ef result ->
  Forall(fun e=>exists v annotation,e=Val v annotation) args ->
  exists final vm' next,ssem_expr(globalenv p) p vm m(App(Val vf tf) args result) final vm' next.
Proof.
  intros. destruct(general_application_entry_configuration _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0)
    as [final [callee [fn [Sigma' [objects' [cells' [packets' [Hstep Hrest]]]]]]]]. eauto.
Qed.

Print Assumptions general_application_progress.

Require Import BeePL_general_call_determinism BeePL_auxlemmas.

Theorem general_application_preservation : forall p globals Gamma Sigma vm m objects cells packets vf tf args result ef
    final vm' next,
  program_runtime_configuration p globals Gamma Sigma vm m objects cells packets(App(Val vf tf) args result) ef result ->
  Forall(fun e=>exists v annotation,e=Val v annotation) args ->
  ssem_expr(globalenv p) p vm m(App(Val vf tf) args result) final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    program_runtime_configuration p globals Gamma Sigma' vm' final objects' cells' packets' next ef' result /\
    sub_effect ef' ef=true.
Proof.
  intros p globals Gamma Sigma vm m objects cells packets vf tf args result ef final vm' next Hconfig Hvalues Hstep.
  pose proof Hconfig as [Hprogram [[Hheap Htyped Hlocations Hframes] Hcoherent]].
  destruct(evaluated_application_function_components _ _ _ _ _ _ _ _ Htyped Hvalues)
    as [types [effects [variadic [Htf [Hef [Hfunction Harguments]]]]]].
  rewrite Htf in Hfunction.
  destruct(typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Hfunction) as [Hnil [Hannotation [b Hv]]]. subst vf.
  destruct(general_application_entry_configuration _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hvalues)
    as [actual [callee [fn [Sigma' [objects' [cells' [packets' [Hactual [Hevol Hafter]]]]]]]]].
  destruct(general_evaluated_application_step_unique _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hactual _ _ _ Hstep)
    as [Hmemory [Hmap Hexpression]]. subst final vm' next.
  exists Sigma',objects',cells',packets',ef;split;[exact Hevol|]. split;[exact Hafter|apply sub_effect_refl].
Qed.

Print Assumptions general_application_preservation.
