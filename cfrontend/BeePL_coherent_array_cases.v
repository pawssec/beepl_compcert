(* Full array expression cases, using only recursive operand/member hypotheses. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_auxlemmas BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_initialized_runtime BeePL_initialized_lists BeePL_coherent_configurations BeePL_coherent_lists.
Require Import BeePL_general_array_reads BeePL_general_array_configurations BeePL_coherent_array_contexts BeePL_strict_progress.
Import ListNotations.

Lemma array_read_value_shape : forall env Gamma Sigma value annotation n elem ef,
  type_expr env Gamma Sigma(Prim(ArrayRead n)[Val value annotation]elem)ef elem ->
  exists b base len attr,value=Vloc b base /\ annotation=Atype elem len attr.
Proof.
  intros * Htyped; inversion Htyped; subst.
  match goal with Hv:type_expr _ _ _(Val _ _) _ (Atype _ _ _) |- _ => inversion Hv; subst end.
  do 4 eexists; auto.
Qed.

Theorem coherent_arrayread_progress_from_operand : forall ge Gamma Sigma vm m objects cells packets p operand n elem ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(Prim(ArrayRead n)[operand]elem)ef elem ->
  (forall arrayType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef arrayType ->
    (exists value annotation,operand=Val value annotation) \/ exists final vm' next,ssem_expr ge p vm m operand final vm' next) ->
  exists final vm' next,ssem_expr ge p vm m(Prim(ArrayRead n)[operand]elem)final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent].
  inversion Htyped; subst.
  match goal with Hoperand:type_expr _ _ _ operand ef (Atype elem ?len ?attr) |- _ =>
    assert(HoperandConfig:coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef (Atype elem len attr))
      by(split;[constructor;assumption|exact Hcoherent]);
    destruct(Hchild _ HoperandConfig) as [[value [annotation Heq]]|[final [vm' [next Hstep]]]] end.
  - subst operand. destruct(array_read_value_shape _ _ _ _ _ _ _ _ Htyped) as [b [base [len0 [attr0 [Hv Ha]]]]]; subst.
    destruct(coherent_general_array_read_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ Hconfig) as [v [objects' [Hstep Hrest]]].
    do 3 eexists; exact Hstep.
  - do 3 eexists; apply ssem_array_read_context; exact Hstep.
Qed.

Theorem coherent_arrayread_preservation_from_operand : forall ge Gamma Sigma vm m objects cells packets p operand n elem ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(Prim(ArrayRead n)[operand]elem)ef elem ->
  (forall arrayType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef arrayType ->
    forall nextM nextVm nextOperand,ssem_expr ge p vm m operand nextM nextVm nextOperand ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextOperand effect' arrayType /\ sub_effect effect' ef=true) ->
  ssem_expr ge p vm m(Prim(ArrayRead n)[operand]elem)final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' elem /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped [Hloc _] [Hframes _]] Hcoherent].
  inversion Hstep; subst.
  - inversion Htyped; subst.
    match goal with Hoperand:type_expr _ _ _ operand ef (Atype elem ?len ?attr), Hs:ssem_expr _ _ _ _ operand _ _ _ |- _ =>
      assert(HoperandConfig:coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets operand ef(Atype elem len attr))
        by(split;[constructor;assumption|exact Hcoherent]);
      destruct(Hchild _ HoperandConfig _ _ _ Hs) as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hnew Hsub]]]]]]];
      destruct(coherent_array_read_operand_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hconfig Hoperand Hs Hevolve Hnew Hsub) as [_ [Hresult Hsubresult]] end.
    exists Sigma',objects',cells',packets',ef'; auto.
  all: destruct(coherent_general_array_read_preservation _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [_ [_ [objects' [Hevolve Hfinal]]]];
    exists Sigma,objects',cells,packets,ef; split;[exact Hevolve|]; split;[exact Hfinal|apply sub_effect_refl].
Qed.

Lemma typed_array_initializer_components : forall env Gamma Sigma arr ty es ef,
  type_expr env Gamma Sigma(Ainit arr ty es ty)ef ty ->
  exists elem len attr ts,ty=Atype elem len attr /\ type_exprs env Gamma Sigma es ef ts.
Proof.
  intros * Htyped; inversion Htyped; subst.
  match goal with Harray:exists attr, _=Atype _ _ attr |- _ => destruct Harray as [attr Harray] end.
  do 4 eexists; eauto.
Qed.

Lemma guarded_array_step_arguments : forall ge p vm m arr ty es final vm' next,
  is_values es=false -> ssem_expr ge p vm m(Ainit arr ty es ty)final vm' next ->
  exists es',next=Ainit arr ty es' ty /\ ssem_exprs ge p vm m es final vm' es'.
Proof.
  intros * Hguard Hstep; inversion Hstep; subst.
  - eexists;split;[reflexivity|apply ssem_cons1; eassumption].
  - eexists;split;[reflexivity|apply ssem_cons2; eassumption].
  - match goal with Hvalues:Forall _ es |- _ => apply all_value_arguments_is_values in Hvalues; congruence end.
Qed.

Theorem coherent_ainit_progress_from_members : forall ge p Gamma Sigma vm m objects cells packets arr ty es ef,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(Ainit arr ty es ty)ef ty ->
  (forall e,In e es -> forall effect elementType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect elementType ->
    (exists value annotation,e=Val value annotation) \/ exists final vm' next,ssem_expr ge p vm m e final vm' next) ->
  exists final vm' next,ssem_expr ge p vm m(Ainit arr ty es ty)final vm' next.
Proof.
  intros * Henv Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct(typed_array_initializer_components _ _ _ _ _ _ _ Htyped) as [elem [len [attr [ts [Hty Hargs]]]]]; subst ty.
  destruct(is_values es) eqn:Hvalues.
  - destruct(coherent_general_array_progress _ p _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hconfig (is_values_all_value_arguments _ Hvalues))
      as [final [fresh [Sigma' [objects' [cells' [packets' [Hstep Hrest]]]]]]]. do 3 eexists;exact Hstep.
  - assert(HargsConfig:coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts)
      by(split;[constructor;assumption|exact Hcoherent]).
    destruct(coherent_list_progress_from_expressions _ _ _ _ _ _ _ _ p _ _ _ HargsConfig Hchild)
      as [final [vm' [es' Hstep]]].
    do 3 eexists; eapply typed_array_arguments_step; eauto.
Qed.

Theorem coherent_ainit_preservation_from_members : forall ge p Gamma Sigma vm m objects cells packets arr ty es ef final vm' next,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets(Ainit arr ty es ty)ef ty ->
  (forall e,In e es -> forall effect elementType,
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e effect elementType ->
    forall nextM nextVm nextElement,ssem_expr ge p vm m e nextM nextVm nextElement ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution ge Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration ge Gamma Sigma' nextVm nextM objects' cells' packets' nextElement effect' elementType /\ sub_effect effect' effect=true) ->
  ssem_expr ge p vm m(Ainit arr ty es ty)final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Henv Hconfig Hchild Hstep.
  pose proof Hconfig as [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct(typed_array_initializer_components _ _ _ _ _ _ _ Htyped) as [elem [len [attr [ts [Hty Hargs]]]]]; subst ty.
  destruct(is_values es) eqn:Hvalues.
  - destruct(coherent_general_array_preservation _ p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Henv Hconfig
      (is_values_all_value_arguments _ Hvalues) Hstep) as [Sigma' [objects' [cells' [packets' [Hevolve Hfinal]]]]].
    exists Sigma',objects',cells',packets',ef; split;[exact Hevolve|];split;[exact Hfinal|apply sub_effect_refl].
  - destruct(guarded_array_step_arguments _ _ _ _ _ _ _ _ _ _ Hvalues Hstep) as [es' [Heq HargsStep]];subst next.
    assert(HargsConfig:coherent_list_configuration ge Gamma Sigma vm m objects cells packets es ef ts)
      by(split;[constructor;assumption|exact Hcoherent]).
    destruct(coherent_list_preservation_from_expressions _ _ _ _ _ _ _ _ p _ _ _ _ _ _ HargsConfig Hchild HargsStep)
      as [Sigma' [objects' [cells' [packets' [ef' [Hevolve [Hargs' Hsub]]]]]]].
    destruct(coherent_array_arguments_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hargs Hvalues HargsStep Hevolve Hargs' Hsub)
      as [_ [Hfinal Hsubfinal]].
    exists Sigma',objects',cells',packets',ef'; auto.
Qed.
Print Assumptions coherent_arrayread_preservation_from_operand.
Print Assumptions coherent_ainit_preservation_from_members.
