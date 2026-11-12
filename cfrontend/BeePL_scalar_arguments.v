(* Scalar call arguments retain both declarative value typing and the location
   evidence needed for reference payloads. No global signature restriction is
   imposed here; only the selected parameter list is constrained. *)
Require Import List AST Maps BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_sem BeePL_substitution_proofs BeePL_soundness_memory BeePL_runtime_locations.
Require Import BeePL_scalar_parameters.

Definition scalar_parameter_values (cenv : bcomposite_env) (Sigma : store_context)
    (L : location_context) (params : list (ident * type)) (values : list value) : Prop :=
  Forall2 (fun param v => scalar_parameter_type (snd param) /\
    type_expr cenv empty_context Sigma (Val v (snd param)) nil (snd param) /\
    value_locations L v (snd param)) params values.

Theorem typed_located_scalar_arguments : forall cenv Gamma Sigma L params es ef,
  type_exprs cenv Gamma Sigma es ef (seq.unzip2 params) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  all_expr_locations (runtime_locations L) es ->
  Forall scalar_parameter_type (seq.unzip2 params) ->
  scalar_parameter_values cenv Sigma L params (extract_values_exprs es).
Proof.
  intros cenv Gamma Sigma L params. induction params as [|[id ty] params IH];
    intros es ef Htyped Hvalues Hlocated Hscalar.
  - inversion Htyped; subst. constructor.
  - inversion Htyped; subst.
    inversion Hvalues as [|head tail Hhead Htail]; subst.
    inversion Hscalar; subst.
    destruct Hhead as [v [annotation Heq]]. subst.
    simpl in Hlocated. destruct Hlocated as [Hheadloc Htailloc].
    match goal with Hvalue : type_expr _ _ _ (Val v annotation) _ ty |- _ =>
      pose proof (type_rel_typeof _ _ _ _ _ _ Hvalue) as Hannotation;
      simpl in Hannotation; subst annotation;
      pose proof (typed_value_effect_nil _ _ _ _ _ _ _ Hvalue) as Hef
    end.
    subst. constructor.
    + split; [assumption |]. split; [|exact Hheadloc].
      eapply value_typing_context_independent; eauto.
    + eapply IH; eauto.
Qed.

Lemma scalar_parameter_values_extend : forall cenv Sigma Sigma' L L' params values,
  store_context_extends Sigma Sigma' ->
  location_context_includes L L' ->
  scalar_parameter_values cenv Sigma L params values ->
  scalar_parameter_values cenv Sigma' L' params values.
Proof.
  intros cenv Sigma Sigma' L L' params values Hstore Hlocations Hvalues.
  unfold scalar_parameter_values in *. induction Hvalues; constructor; auto.
  destruct H as [Hscalar [Htyped Hlocated]]. split; [exact Hscalar |]. split.
  - eapply (proj2 typing_store_extension); eauto.
  - eapply value_locations_monotone; eauto.
Qed.

Print Assumptions typed_located_scalar_arguments.
Print Assumptions scalar_parameter_values_extend.
