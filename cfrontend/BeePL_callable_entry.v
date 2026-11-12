(* Callable locations certify code identity; this separate environment contract
   certifies function bodies and the parameter signatures currently handled by
   constructive call entry. Neither is inferred from an arbitrary code pointer. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_call_entry.
Require Import BeePL_callable_variables BeePL_callable_state BeePL_call_state.
Import ListNotations.

Definition primitive_internal_code_contract (bge : genv) (globals : ty_context)
    (Sigma : store_context) : Prop :=
  forall b fn,
    Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    type_function bge.(genv_cenv) globals Sigma fn /\
    Forall (fun param => exists pt, snd param = Vtype pt /\
      type_is_volatile (transBeePL_type (Vtype pt)) = false) fn.(fn_args).

Lemma function_typing_store_extension : forall cenv Gamma Sigma Sigma' fn,
  type_function cenv Gamma Sigma fn -> store_context_extends Sigma Sigma' ->
  type_function cenv Gamma Sigma' fn.
Proof.
  intros cenv Gamma Sigma Sigma' fn Htyped Hext. inversion Htyped; subst.
  eapply ty_function; eauto. eapply (proj2 typing_store_extension); eauto.
Qed.

Lemma primitive_code_contract_store_extension : forall bge globals Sigma Sigma',
  primitive_internal_code_contract bge globals Sigma ->
  store_context_extends Sigma Sigma' ->
  primitive_internal_code_contract bge globals Sigma'.
Proof.
  intros bge globals Sigma Sigma' Hcode Hext b fn Hfind.
  destruct (Hcode b fn Hfind) as [Htyped Hparams]. split; [|exact Hparams].
  eapply function_typing_store_extension; eauto.
Qed.

Lemma typed_arguments_annotations : forall cenv Gamma Sigma es ef ts,
  type_exprs cenv Gamma Sigma es ef ts -> typeof_exprs es = ts.
Proof.
  intros cenv Gamma Sigma es ef ts Htyped. induction Htyped; simpl; auto.
  rewrite (type_rel_typeof _ _ _ _ _ _ H), IHHtyped. reflexivity.
Qed.

Lemma primitive_evaluated_arguments : forall cenv Gamma Sigma es ef (params : list (ident * type)),
  type_exprs cenv Gamma Sigma es ef (seq.unzip2 params) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  Forall (fun param => exists pt, snd param = Vtype pt /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false) params ->
  Forall2 (fun param v => exists pt, snd param = Vtype pt /\
    typeof_value v (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    params (extract_values_exprs es).
Proof.
  intros cenv Gamma Sigma es ef params. revert es ef.
  induction params as [|[id ty] params IH]; intros es ef Htyped Hvalues Hparams.
  - inversion Htyped; subst. constructor.
  - inversion Hparams as [|param rest Hparam Hparams_tail]; subst.
    inversion Htyped; subst.
    inversion Hvalues as [|head tail Hhead Htail]; subst.
    destruct Hhead as [v [annotation Heq]]. subst.
    destruct Hparam as [pt [Hty Hvolatile]]. simpl in Hty. subst ty.
    simpl. constructor.
    + exists pt. simpl. split; [reflexivity |]. split; [|exact Hvolatile].
      match goal with Hval : type_expr _ _ _ (Val v ?a) _ (Vtype pt) |- _ =>
        pose proof (type_rel_typeof _ _ _ _ _ _ Hval) as Hannotation;
        simpl in Hannotation; subst a;
        eapply type_rel_typeof_val; exact Hval
      end.
    + eapply IH; eauto.
Qed.

Print Assumptions primitive_code_contract_store_extension.
Print Assumptions primitive_evaluated_arguments.

(* Resolution and primitive argument initialization now follow from the
   concrete runtime code invariant and the declarative argument typing. *)
Theorem typed_located_primitive_call_entry :
  forall bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects,
  primitive_internal_code_contract bge globals Sigma ->
  type_expr bge.(genv_cenv) Gamma Sigma (Val v annotation) fn_effects
    (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations bge layout) (Val v annotation) ->
  type_exprs bge.(genv_cenv) Gamma Sigma es argument_effects args ->
  Forall (fun e => exists value ty, e = Val value ty) es ->
  callable_heap_state Gamma Sigma bge caller m layout ->
  callable_variable_layout globals Sigma bge empty_vmap layout ->
  (forall b fn, Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (callable_heap_locations bge layout) fn.(fn_body)) ->
  exists fn callee initialized Sigma',
    ssem_expr bge p caller m (App (Val v annotation) es result)
      initialized caller (CallFrame callee fn.(fn_body) result) /\
    store_context_extends Sigma Sigma' /\
    primitive_internal_code_contract bge globals Sigma' /\
    callable_heap_state Gamma Sigma' bge caller initialized
      (extended_call_layout layout callee fn.(fn_args)) /\
    callable_heap_state (bind_vars globals fn.(fn_args)) Sigma' bge callee initialized
      (extended_call_layout layout callee fn.(fn_args)) /\
    type_expr bge.(genv_cenv) Gamma Sigma'
      (CallFrame callee fn.(fn_body) result) effects result /\
    runtime_locations (callable_heap_locations bge
      (extended_call_layout layout callee fn.(fn_args)))
      (CallFrame callee fn.(fn_body) result) /\
    Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) /\
    type_expr bge.(genv_cenv) (bind_vars globals fn.(fn_args)) Sigma'
      fn.(fn_body) effects result.
Proof.
  intros bge Gamma globals Sigma p caller m layout v annotation fn_effects
    args effects result variadic es argument_effects
    Hcode Hfunction Hlocation Harguments Hvalues Hcaller Hglobals Hbodies.
  destruct (located_function_value _ _ _ _ _ _ _ _ _ _ _ Hfunction Hlocation)
    as [b [fn [Hv [Hannotation [Hef [Hfind Hsignature]]]]]].
  subst v annotation fn_effects.
  destruct (Hcode b fn Hfind) as [Hfn Hparameters].
  unfold type_of_function in Hsignature. inversion Hsignature; subst args effects result variadic.
  assert (Hshapes : Forall2 (fun param value => exists pt,
    snd param = Vtype pt /\ typeof_value value (Vtype pt) /\
    type_is_volatile (transBeePL_type (Vtype pt)) = false)
    (fn_args fn) (extract_values_exprs es)).
  { eapply primitive_evaluated_arguments; eauto. }
  assert (Htypes : typeof_exprs es = seq.unzip2 (fn_args fn)) by
    (eapply typed_arguments_annotations; eauto).
  inversion Hfn; subst.
  assert (Hnames : NoDup (map fst (fn_args fn))) by
    (apply parameter_names_nodup; assumption).
  destruct (primitive_callable_state_preparation bge Gamma globals Sigma caller m layout
    (fn_args fn) (extract_values_exprs es) Hnames Hshapes Hcaller Hglobals)
    as [callee [allocated [initialized [Sigma'
      [Halloc [Hbind [Hext [Hcaller' Hcallee']]]]]]]].
  exists fn, callee, initialized, Sigma'. split.
  - rewrite <- Htypes. eapply ssem_app3; eauto; reflexivity.
  - split; [exact Hext |]. split.
    + eapply primitive_code_contract_store_extension; eauto.
    + split; [exact Hcaller' |]. split; [exact Hcallee' |]. split.
      * eapply ty_callframe. eapply (proj2 typing_store_extension); eauto.
      * split.
        -- simpl. eapply runtime_locations_monotone; [|apply (Hbodies b fn Hfind)].
           apply callable_heap_locations_monotone. intros block ofs ty chunk Hentry. left; exact Hentry.
        -- split; [exact Hfind |]. eapply (proj2 typing_store_extension); eauto.
Qed.

Print Assumptions typed_located_primitive_call_entry.
