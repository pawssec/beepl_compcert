(* App context assembly. The sole nonrecursive obligation here is the
   evaluated call head; this conditional lemma is not final soundness. *)
Require Import List Bool Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_initialized_runtime.
Require Import BeePL_initialized_lists BeePL_initialized_contexts BeePL_coherent_lists.
Require Import BeePL_coherent_configurations BeePL_strict_progress BeePL_type_equality.
Require Import BeePL_substitution_proofs BeePL_auxlemmas.
Import ListNotations.

Definition evaluated_application_obligation : Prop :=
 forall value annotation args result,
 Forall(fun e=>exists v ty,e=Val v ty) args ->
 program_expression_safe(App(Val value annotation) args result).

Lemma application_typing_parts : forall env Gamma Sigma fn args rt ef,
 type_expr env Gamma Sigma(App fn args rt)ef rt ->
 exists fty variadic types calls fe ae,
 ef=fe++calls++ae /\ type_expr env Gamma Sigma fn fe fty /\
 (eq_type fty(Ptrtype(Fptype types calls rt variadic)) ||eq_type fty(Ftype types calls rt variadic))=true /\
 type_exprs env Gamma Sigma args ae types.
Proof. intros * H;inversion H;subst;do 6 eexists;repeat split;eassumption||reflexivity. Qed.

Lemma callable_literal_location : forall env Gamma Sigma v annotation ef fty types calls rt variadic,
 type_expr env Gamma Sigma(Val v annotation)ef fty ->
 (eq_type fty(Ptrtype(Fptype types calls rt variadic)) ||eq_type fty(Ftype types calls rt variadic))=true ->
 exists b base,v=Vloc b base.
Proof.
 intros * Htyped Hsig. apply orb_true_iff in Hsig;destruct Hsig as [Hsig|Hsig];apply eq_type_sound in Hsig;subst fty;inversion Htyped;subst;eauto.
Qed.

Theorem program_application_case : forall fn args rt,
 evaluated_application_obligation -> program_expression_safe fn ->
 Forall program_expression_safe args -> program_expression_safe(App fn args rt).
Proof.
 intros fn args rt Hhead HfnIH HargsIH. split.
 - unfold program_expression_progress;intros p globals Gamma Sigma vm m objects cells packets ef ty Hprogram.
   pose proof Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped [Hfloc Haloc] [Hfframes Haframes]] Hcoherent].
   pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hann;simpl in Hann;subst ty.
   destruct(application_typing_parts _ _ _ _ _ _ _ Htyped) as [fty [variadic [types [calls [fe [ae [Hef [Hfn [Hsig Hargs]]]]]]]]]. subst ef.
   assert(HfnConfig:coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets fn fe fty) by (split;[constructor;assumption|exact Hcoherent]).
   assert(HargsConfig:coherent_list_configuration(globalenv p) Gamma Sigma vm m objects cells packets args ae types) by (split;[constructor;assumption|exact Hcoherent]).
   destruct(program_child_progress fn HfnIH p globals Gamma Sigma vm m objects cells packets fe fty Hcode HfnConfig)
   as [[v [annotation Heq]]|[final [vm' [next Hstep]]]].
   + subst fn. destruct(is_values args) eqn:Hvalues.
     * apply is_values_all_value_arguments in Hvalues.
       destruct(proj1(Hhead v annotation args rt Hvalues) _ _ _ _ _ _ _ _ _ _ _ Hprogram) as [[v' [annotation' Heq]]|Hstep];[discriminate|right;exact Hstep].
     * destruct(callable_literal_location _ _ _ _ _ _ _ _ _ _ _ Hfn Hsig) as [b [base Hv]];subst v.
       destruct(program_list_progress args HargsIH p globals Gamma Sigma vm m objects cells packets ae types Hcode HargsConfig)
       as [final [vm' [next Hstep]]]. right;exists final,vm',(App(Val(Vloc b base)annotation)next rt). apply ssem_app2;assumption.
   + right;exists final,vm',(App next args rt);apply ssem_app1;exact Hstep.
 - unfold program_expression_preservation;intros p globals Gamma Sigma vm m objects cells packets ef ty final vm' next Hprogram Hstep.
   pose proof Hprogram as [Hcode Hconfig].
   pose proof Hconfig as [[Hheap Htyped [Hfloc Haloc] [Hfframes Haframes]] Hcoherent].
   pose proof(type_rel_typeof _ _ _ _ _ _ Htyped) as Hann;simpl in Hann;subst ty.
   destruct(application_typing_parts _ _ _ _ _ _ _ Htyped) as [fty [variadic [types [calls [fe [ae [Hef [Hfn [Hsig Hargs]]]]]]]]]. subst ef.
   assert(HfnConfig:coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets fn fe fty) by (split;[constructor;assumption|exact Hcoherent]).
   assert(HargsConfig:coherent_list_configuration(globalenv p) Gamma Sigma vm m objects cells packets args ae types) by (split;[constructor;assumption|exact Hcoherent]).
   inversion Hstep;subst.
   + eapply program_result_lift;[exact Hprogram|].
     match goal with Hs:ssem_expr _ _ _ _ fn _ _ _ |- _ =>
     destruct(program_child_preservation fn HfnIH p globals Gamma Sigma vm m objects cells packets fe fty _ _ _ Hcode HfnConfig Hs)
     as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [[Hnew Hcoherent'] Hsub]]]]]]];
     destruct(initialized_application_function_context (globalenv p) Gamma Sigma vm m objects cells packets p fn args rt fty variadic types calls fe ae
      Sigma' vm' final objects' cells' packets' _ ef'
      (proj1 Hconfig) Hfn Hsig Hargs Hs Hevolve Hnew Hsub) as [_ [Hparent HparentSub]]
     end.
     do 4 eexists;eexists;split;[exact Hevolve|]. split;[split;[exact Hparent|exact Hcoherent']|exact HparentSub].
   + eapply program_result_lift;[exact Hprogram|].
     pose proof(typed_value_effect_nil _ _ _ _ _ _ _ Hfn) as Hnil;subst fe;simpl in Hprogram,Hconfig.
     pose proof(type_rel_typeof _ _ _ _ _ _ Hfn) as Hannotation;simpl in Hannotation;subst fty.
     match goal with Hs:ssem_exprs _ _ _ _ args _ _ _ |- _ =>
     destruct(program_list_preservation args HargsIH p globals Gamma Sigma vm m objects cells packets ae types _ _ _ Hcode HargsConfig Hs)
     as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [[Hnew Hcoherent'] Hsub]]]]]]];
     destruct(initialized_application_arguments_context (globalenv p) Gamma Sigma vm m objects cells packets p _ _ _ types calls rt variadic args ae
      Sigma' vm' final objects' cells' packets' _ ef'
      (proj1 Hconfig) Hfn Hsig ltac:(assumption) Hs Hevolve Hnew Hsub) as [_ [Hparent HparentSub]]
     end.
     do 4 eexists;eexists;split;[exact Hevolve|]. split;[split;[exact Hparent|exact Hcoherent']|exact HparentSub].
   all: match goal with Hv:Forall(fun e=>exists v ty,e=Val v ty) ?actualArgs |- _ =>
    eapply (proj2(Hhead _ _ actualArgs _ Hv));[exact Hprogram|exact Hstep]
   end.
Qed.
