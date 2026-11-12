(* Code parameters alias authentic immutable function addresses. Mutable data
   parameters retain their own fresh allocations. *)
Require Import List Bool ZArith Coqlib Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_runtime_locations.
Require Import BeePL_callable_locations BeePL_scalar_parameters BeePL_call_parameters.
Require Import BeePL_scalar_call_layout.
Import ListNotations.

Lemma nonfunction_parameters_no_code : forall params,
  Forall (fun param => is_funtype (snd param) = false) params ->
  ~ has_function_parameter params.
Proof.
  intros params Hall [id [args [effects [result [variadic Hin]]]]].
  rewrite Forall_forall in Hall. specialize (Hall _ Hin). discriminate Hall.
Qed.

Lemma call_parameters_no_code : forall params,
  Forall call_parameter_type (seq.unzip2 params) -> ~ has_function_parameter params.
Proof.
  intros params Hall. apply nonfunction_parameters_no_code.
  induction params as [|[id ty] params IH]; simpl in *; [constructor|].
  inversion Hall; subst. constructor; [|apply IH; assumption].
  destruct H1 as [Hunit|Hscalar]; [subst ty; reflexivity|].
  apply scalar_parameter_not_function; exact Hscalar.
Qed.

Lemma function_partition_data_in : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  forall item, In item data -> In item params.
Proof.
  intros ge params values codes data data_values Hpartition. induction Hpartition; intros item Hin; simpl in *.
  - contradiction.
  - right; auto.
  - destruct Hin; [left; assumption|right; auto].
Qed.

Lemma function_partition_data_nonfunction : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  Forall (fun param => is_funtype (snd param) = false) data.
Proof. intros ge params values codes data data_values H; induction H; simpl; auto. Qed.

Lemma function_partition_data_names : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  NoDup (map fst params) -> NoDup (map fst data).
Proof.
  intros ge params values codes data data_values Hpartition. induction Hpartition; intros Hnames; simpl in *.
  - constructor.
  - inversion Hnames; subst; auto.
  - inversion Hnames; subst. constructor; [|auto]. intro Hin.
    apply in_map_iff in Hin as [[name ty'] [Heq Hin]]. simpl in Heq; subst name.
    apply H2. apply in_map_iff. exists (id, ty'). split; [reflexivity|].
    eapply function_partition_data_in; eauto.
Qed.

Lemma function_partition_code_origin : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  forall id b ty, PTree.get id codes = Some (b, ty) ->
    In (id, ty) params /\ internal_code_locations ge b Ptrofs.zero ty.
Proof.
  intros ge params values codes data data_values Hpartition. induction Hpartition; intros name block ty' Hget.
  - unfold empty_vmap in Hget. rewrite PTree.gempty in Hget. discriminate.
  - rewrite PTree.gsspec in Hget. destruct (peq name id) as [Heq|Hneq].
    + subst name. inversion Hget; subst block ty'. split; [left; reflexivity|].
      split; [reflexivity|]. exists args, effects, result, variadic, fn. repeat split; auto.
    + destruct (IHHpartition _ _ _ Hget) as [Hin Hcode]. split; [right; exact Hin|exact Hcode].
  - destruct (IHHpartition _ _ _ Hget) as [Hin Hcode]. split; [right; exact Hin|exact Hcode].
Qed.

Lemma function_partition_code_missing : forall ge params values codes data data_values id,
  function_parameter_partition ge params values codes data data_values ->
  ~ In id (map fst params) -> PTree.get id codes = None.
Proof.
  intros ge params values codes data data_values id Hpartition Hmissing.
  destruct (PTree.get id codes) as [[b ty]|] eqn:Hget; [|reflexivity].
  exfalso. apply Hmissing. apply in_map_iff. exists (id, ty). split; [reflexivity|].
  exact (proj1 (function_partition_code_origin _ _ _ _ _ _ Hpartition _ _ _ Hget)).
Qed.

Lemma function_partition_unique : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  forall codes' data' data_values',
  function_parameter_partition ge params values codes' data' data_values' ->
  codes' = codes /\ data' = data /\ data_values' = data_values.
Proof.
  intros ge params values codes data data_values Hpartition. induction Hpartition;
    intros codes' data' data_values' Hother; inversion Hother; subst;
    try discriminate.
  - auto.
  - match goal with Htail : function_parameter_partition _ params values _ _ _ |- _ =>
      destruct (IHHpartition _ _ _ Htail) as [Hcodes [Hdata Hvalues]] end.
    subst. auto.
  - match goal with Htail : function_parameter_partition _ params values _ _ _ |- _ =>
      destruct (IHHpartition _ _ _ Htail) as [Hcodes [Hdata Hvalues]] end.
    subst. auto.
Qed.

Print Assumptions call_parameters_no_code.
Print Assumptions function_partition_data_names.
Print Assumptions function_partition_code_origin.
Print Assumptions function_partition_unique.

Definition code_or_data_parameter_values (ge : genv) (Sigma : store_context)
    (L : location_context) (params : list (ident * type)) (values : list value) : Prop :=
  Forall2 (fun param v =>
    (call_parameter_type (snd param) \/ is_funtype (snd param) = true) /\
    type_expr ge.(genv_cenv) empty_context Sigma (Val v (snd param)) nil (snd param) /\
    value_locations L v (snd param)) params values.

Theorem located_function_parameter_partition : forall ge Sigma L params values,
  (forall b args effects result variadic,
    L b Ptrofs.zero (Ftype args effects result variadic) ->
    internal_code_locations ge b Ptrofs.zero (Ftype args effects result variadic)) ->
  code_or_data_parameter_values ge Sigma L params values ->
  exists codes data data_values,
    function_parameter_partition ge params values codes data data_values /\
    call_parameter_values ge.(genv_cenv) Sigma L data data_values.
Proof.
  intros ge Sigma L params values Hcode Hvalues. induction Hvalues as [|[id ty] v params values Hhead Htail IH].
  - exists empty_vmap, [], []. split; constructor.
  - destruct IH as [codes [data [data_values [Hpartition Hdata]]]].
    destruct Hhead as [Hsupported [Htyped Hlocated]]. simpl in Hsupported, Htyped, Hlocated.
    destruct (is_funtype ty) eqn:Hfun.
    + destruct ty; try discriminate Hfun.
      destruct (typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Htyped)
        as [Hnil [Hannotation [codeblock Hv]]]. subst v.
      specialize (Hcode codeblock _ _ _ _ Hlocated).
      destruct Hcode as [Hz [args [effects [result [variadic [fn [Hsig [Hfind Htype]]]]]]]].
      inversion Hsig; subst.
      eexists; exists data, data_values. split; [eapply function_partition_code; eauto|exact Hdata].
    + exists codes, ((id, ty) :: data), (v :: data_values). split.
      * apply function_partition_data; assumption.
      * constructor; [|exact Hdata]. simpl. split; [destruct Hsupported; congruence|]. split; assumption.
Qed.

Print Assumptions located_function_parameter_partition.

Lemma typed_located_code_or_data_arguments : forall ge Gamma Sigma L params es ef,
  type_exprs ge.(genv_cenv) Gamma Sigma es ef (seq.unzip2 params) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  all_expr_locations (runtime_locations L) es ->
  Forall (fun ty => call_parameter_type ty \/ is_funtype ty = true) (seq.unzip2 params) ->
  code_or_data_parameter_values ge Sigma L params (extract_values_exprs es).
Proof.
  intros ge Gamma Sigma L params. induction params as [|[id ty] params IH];
    intros es ef Htyped Hvalues Hlocated Htypes.
  - inversion Htyped; subst. constructor.
  - inversion Htyped; subst. inversion Hvalues as [|head tail Hhead Htail]; subst.
    inversion Htypes; subst. destruct Hhead as [v [annotation Heq]]. subst.
    simpl in Hlocated. destruct Hlocated as [Hheadloc Htailloc].
    match goal with Hvalue : type_expr _ _ _ (Val v annotation) _ ty |- _ =>
      pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
      simpl in Hannotation; subst annotation;
      pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hef
    end. subst. constructor.
    + split; [assumption |]. split; [|exact Hheadloc].
      eapply value_typing_context_independent; eauto.
    + eapply IH; eauto.
Qed.


Lemma unique_parameter_type : forall (params : list (ident * type)) id ty ty',
  NoDup (map fst params) -> In (id, ty) params -> In (id, ty') params -> ty = ty'.
Proof.
  induction params as [|[name t] params IH]; intros id ty ty' Hnames Hin Hin'; [contradiction|].
  inversion Hnames as [|? ? Hmissing Htail]; subst.
  destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin']; try congruence.
  - inversion Heq; subst. exfalso. apply Hmissing. apply in_map_iff. exists (id, ty'). auto.
  - inversion Heq'; subst. exfalso. apply Hmissing. apply in_map_iff. exists (id, ty). auto.
  - eapply IH; eauto.
Qed.

Lemma function_partition_parameter_origin : forall ge params values codes data data_values,
  function_parameter_partition ge params values codes data data_values ->
  NoDup (map fst params) ->
  forall id ty, In (id, ty) params -> In (id, ty) data \/
    exists b, PTree.get id codes = Some (b, ty) /\ internal_code_locations ge b Ptrofs.zero ty.
Proof.
  intros ge params values codes data data_values Hpartition. induction Hpartition;
    intros Hnames name t Hin; [contradiction| |].
  - inversion Hnames as [|? ? Hmissing Htail]; subst.
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst name t. right. exists b. split; [apply PTree.gss|].
      split; [reflexivity|]. exists args, effects, result, variadic, fn. repeat split; auto.
    + destruct (IHHpartition Htail name t Hin) as [Hdata|[block [Hget Hcode]]]; [left; exact Hdata|].
      right. exists block. split; [|exact Hcode]. rewrite PTree.gso; [exact Hget|].
      intro Heq; subst name. apply Hmissing. apply in_map_iff. exists (id,t). auto.
  - inversion Hnames as [|? ? Hmissing Htail]; subst.
    destruct Hin as [Heq|Hin]; [left; left; exact Heq|].
    destruct (IHHpartition Htail name t Hin) as [Hdata|Hcode]; [left; right; exact Hdata|right; exact Hcode].
Qed.

Lemma function_partition_code_not_data : forall ge params values codes data data_values id b ty,
  function_parameter_partition ge params values codes data data_values ->
  NoDup (map fst params) -> PTree.get id codes = Some (b, ty) ->
  ~ In id (map fst data).
Proof.
  intros ge params values codes data data_values id b ty Hpartition Hnames Hget Hin.
  destruct (function_partition_code_origin _ _ _ _ _ _ Hpartition _ _ _ Hget) as [Hparam Hcode].
  apply in_map_iff in Hin as [[name t] [Heq Hin]]. simpl in Heq; subst name.
  assert (t = ty) by (eapply unique_parameter_type; eauto using function_partition_data_in). subst t.
  pose proof (function_partition_data_nonfunction _ _ _ _ _ _ Hpartition) as Hall.
  rewrite Forall_forall in Hall. specialize (Hall _ Hin). simpl in Hall.
  destruct Hcode as [Hz [args [effects [result [variadic [fn [Hty Hrest]]]]]]]. subst ty. discriminate Hall.
Qed.

Lemma function_full_assignment_impossible : forall ge args effects result variadic m b ofs v final stored,
  ~ assign_addr ge (Ftype args effects result variadic) m b ofs Full v final stored.
Proof. intros ge args effects result variadic m b ofs v final stored Hassign.
  inversion Hassign; subst; discriminate. Qed.

Lemma binding_parameters_exclude_functions : forall ge vm m params values final,
  bind_variables ge vm m params values final ->
  Forall (fun param => is_funtype (snd param) = false) params.
Proof.
  intros ge vm m params values final Hbind. induction Hbind; constructor; auto.
  destruct ty; try reflexivity. exfalso. eapply function_full_assignment_impossible; eauto.
Qed.

Lemma function_parameters_cannot_use_data_binding : forall ge vm m params values final,
  has_function_parameter params -> ~ bind_variables ge vm m params values final.
Proof. intros ge vm m params values final Hhas Hbind.
  eapply nonfunction_parameters_no_code; [eapply binding_parameters_exclude_functions; exact Hbind|exact Hhas]. Qed.
