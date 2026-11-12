(* Exhaustive Match assembly: valid typing selects the existing option or
   Bytes head semantics, while scrutinee steps use the structural IH. *)
Require Import List Bool ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_substitution_proofs.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_option_cases BeePL_initialized_packet_header.
Import ListNotations.

Lemma valid_match_patterns_length : forall ty ps,
  valid_match_patterns ty ps -> length ps=2%nat.
Proof.
  intros ty ps H. destruct ty; simpl in H; try contradiction.
  - destruct p; simpl in H; try contradiction. destruct H as [x [H|H]]; subst; reflexivity.
  - destruct H as [header [schema [fields [rest H]]]]; subst; reflexivity.
Qed.

Lemma typed_match_two_branches : forall env Gamma Sigma scrutinee ps es ef ty,
  type_expr env Gamma Sigma (Match scrutinee ps es ty) ef ty ->
  exists p1 p2 yes no, ps=[p1;p2] /\ es=[yes;no].
Proof.
  intros * Htyped. inversion Htyped; subst.
  match goal with Hpatterns : valid_match_patterns _ ps, Hlength : length ps=length es |- _ =>
    pose proof(valid_match_patterns_length _ _ Hpatterns) as Hps;
    assert(Hes:length es=2%nat) by lia
  end.
  destruct ps as [|p1 [|p2 [|extra ps]]]; simpl in Hps; try discriminate.
  destruct es as [|yes [|no [|extra es]]]; simpl in Hes; try discriminate.
  exists p1,p2,yes,no; auto.
Qed.

Lemma typed_match_value_cases : forall env Gamma Sigma value annotation ps es ef ty,
  type_expr env Gamma Sigma (Match (Val value annotation) ps es ty) ef ty ->
  (exists payload pt, value=Voption payload /\ annotation=Ptrtype(Otype pt)) \/
  (exists b ofs sid header rest fields yes no, value=Vloc b ofs /\ annotation=Bytes /\
    ps=[Pbytes header(Stype sid noattr)fields;Pbytes rest Bytes []] /\ es=[yes;no]).
Proof.
  intros * Htyped. pose proof(typed_match_two_branches _ _ _ _ _ _ _ _ Htyped)
    as [p1 [p2 [yes [no [Hps Hes]]]]].
  inversion Htyped; subst.
  match goal with Hscrut : type_expr _ _ _ (Val _ _) _ _ |- _ => inversion Hscrut; subst end;
    match goal with Hpatterns : valid_match_patterns _ _ |- _ => simpl in Hpatterns end;
    try contradiction.
  - right. match goal with Hpatterns : exists header schema fields rest, _ |- _ =>
      destruct Hpatterns as [header [schema [fields [rest Hpatterns]]]] end.
    do 8 eexists; repeat split; eauto.
  - left. do 2 eexists; auto.
Qed.

Theorem coherent_match_value_progress : forall p Gamma Sigma vm m objects cells packets value annotation ps es ef ty,
  coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets
    (Match(Val value annotation)ps es ty)ef ty ->
  exists final vm' next, ssem_expr(globalenv p)p vm m(Match(Val value annotation)ps es ty)final vm' next.
Proof.
  intros * Hconfig.
  destruct(typed_match_value_cases _ _ _ _ _ _ _ _ _ (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)))
    as [[payload [pt [Hv Ha]]]|[b [ofs [sid [header [rest [fields [yes [no [Hv [Ha [Hp He]]]]]]]]]]]]; subst.
  - destruct(coherent_option_match_head_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig)
      as [next [effect [Hstep Hrest]]]. do 3 eexists; exact Hstep.
  - destruct(coherent_bytes_match_head_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig)
      as [final [next [Sigma' [objects' [cells' [effect [Hstep Hrest]]]]]]].
    do 3 eexists; exact Hstep.
Qed.

Theorem coherent_match_value_preservation : forall p Gamma Sigma vm m objects cells packets value annotation ps es ef ty final vm' next,
  coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets
    (Match(Val value annotation)ps es ty)ef ty ->
  ssem_expr(globalenv p)p vm m(Match(Val value annotation)ps es ty)final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution(globalenv p)Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration(globalenv p)Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hstep.
  destruct(typed_match_value_cases _ _ _ _ _ _ _ _ _ (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)))
    as [[payload [pt [Hv Ha]]]|[b [ofs [sid [header [rest [fields [yes [no [Hv [Ha [Hp He]]]]]]]]]]]]; subst.
  - eapply coherent_option_match_head_preservation; eauto.
  - destruct(coherent_bytes_match_head_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hstep)
      as [_ [Sigma' [objects' [cells' [effect [Hevolve [Hfinal Hsub]]]]]]].
    exists Sigma',objects',cells',packets,effect; auto.
Qed.

Theorem coherent_match_progress_from_scrutinee : forall p Gamma Sigma vm m objects cells packets scrutinee ps es ef ty,
  coherent_runtime_configuration(globalenv p)Gamma Sigma vm m objects cells packets(Match scrutinee ps es ty)ef ty ->
  (forall effect scrutineeTy,
    coherent_runtime_configuration(globalenv p)Gamma Sigma vm m objects cells packets scrutinee effect scrutineeTy ->
    (exists v annotation,scrutinee=Val v annotation) \/ exists final vm' next,ssem_expr(globalenv p)p vm m scrutinee final vm' next) ->
  exists final vm' next,ssem_expr(globalenv p)p vm m(Match scrutinee ps es ty)final vm' next.
Proof.
  intros * Hconfig Hchild.
  pose proof Hconfig as [[Hheap Htyped [Hsloc Hbloc] [Hsframes Hbframes]] Hcoherent].
  destruct(typed_match_two_branches _ _ _ _ _ _ _ _ Htyped) as [p1 [p2 [yes [no [Hp He]]]]]; subst ps es.
  inversion Htyped; subst.
  match goal with Hscrut : type_expr _ _ _ scrutinee ?se ?sty |- _ =>
    assert(HscrutConfig:coherent_runtime_configuration(globalenv p)Gamma Sigma vm m objects cells packets scrutinee se sty)
      by(split;[constructor;assumption|exact Hcoherent]);
    destruct(Hchild se sty HscrutConfig) as [[value [annotation Heq]]|[final [vm' [next Hstep]]]] end.
  - subst scrutinee. eapply coherent_match_value_progress; exact Hconfig.
  - do 3 eexists; apply ssem_match_none1; exact Hstep.
Qed.

Theorem coherent_match_preservation_from_scrutinee : forall p Gamma Sigma vm m objects cells packets scrutinee ps es ef ty final vm' next,
  coherent_runtime_configuration(globalenv p)Gamma Sigma vm m objects cells packets(Match scrutinee ps es ty)ef ty ->
  (forall effect scrutineeTy,
    coherent_runtime_configuration(globalenv p)Gamma Sigma vm m objects cells packets scrutinee effect scrutineeTy ->
    forall nextM nextVm nextScrutinee,ssem_expr(globalenv p)p vm m scrutinee nextM nextVm nextScrutinee ->
    exists Sigma' objects' cells' packets' effect',
      initialized_heap_evolution(globalenv p)Sigma objects cells packets Sigma' nextM objects' cells' packets' /\
      coherent_runtime_configuration(globalenv p)Gamma Sigma' nextVm nextM objects' cells' packets' nextScrutinee effect' scrutineeTy /\
      sub_effect effect' effect=true) ->
  ssem_expr(globalenv p)p vm m(Match scrutinee ps es ty)final vm' next ->
  exists Sigma' objects' cells' packets' ef',
    initialized_heap_evolution(globalenv p)Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration(globalenv p)Gamma Sigma' vm' final objects' cells' packets' next ef' ty /\ sub_effect ef' ef=true.
Proof.
  intros * Hconfig Hchild Hstep. inversion Hstep; subst;
    try solve[eapply coherent_match_value_preservation; eauto].
  match goal with Hs:ssem_expr _ _ _ _ scrutinee _ _ _ |- _ =>
    destruct(coherent_match_context _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ _ _ Hconfig Hs
      ltac:(intros effect sty Hscrut; eapply Hchild; eauto))
      as [Sigma' [objects' [cells' [packets' [effect' [_ [Hevolve [Hfinal Hsub]]]]]]]] end.
  exists Sigma',objects',cells',packets',effect'; auto.
Qed.
Print Assumptions coherent_match_progress_from_scrutinee.
Print Assumptions coherent_match_preservation_from_scrutinee.
