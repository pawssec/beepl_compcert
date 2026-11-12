(* Call arguments may be unit or have supported scalar storage. Unit arguments
   carry no bytes; they are consumed by the explicit no-store binding rule. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_runtime_locations.
Require Import BeePL_scalar_parameters BeePL_scalar_parameter_allocations.
Import ListNotations.

Definition call_parameter_type (ty : type) : Prop :=
  ty = Utype \/ scalar_parameter_type ty.

Definition call_parameter_values cenv Sigma L (params : list (ident * type))
    (values : list value) : Prop :=
  Forall2 (fun param v => call_parameter_type (snd param) /\
    type_expr cenv empty_context Sigma (Val v (snd param)) nil (snd param) /\
    value_locations L v (snd param)) params values.

Definition call_parameter_inputs cenv Sigma L (vm : vmap) (m : Mem.mem)
    (params : list (ident * type)) (values : list value) : Prop :=
  Forall2 (fun param v => exists b,
    PTree.get (fst param) vm = Some (b, snd param) /\
    ((snd param = Utype /\ v = Vunit) \/
     (scalar_parameter_type (snd param) /\
      type_expr cenv empty_context Sigma (Val v (snd param)) nil (snd param) /\
      value_locations L v (snd param) /\
      Mem.valid_access m (transl_bchunk_cchunk (scalar_parameter_chunk (snd param)))
        b 0 Freeable))) params values.

Lemma typed_located_call_arguments : forall cenv Gamma Sigma L params es ef,
  type_exprs cenv Gamma Sigma es ef (seq.unzip2 params) ->
  Forall (fun e => exists v ty, e = Val v ty) es ->
  all_expr_locations (runtime_locations L) es ->
  Forall call_parameter_type (seq.unzip2 params) ->
  call_parameter_values cenv Sigma L params (extract_values_exprs es).
Proof.
  intros cenv Gamma Sigma L params. induction params as [|[id ty] params IH];
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

Lemma call_parameter_values_extend : forall cenv Sigma Sigma' L L' params values,
  store_context_extends Sigma Sigma' -> location_context_includes L L' ->
  call_parameter_values cenv Sigma L params values ->
  call_parameter_values cenv Sigma' L' params values.
Proof.
  intros cenv Sigma Sigma' L L' params values Hext Hinc Hvalues.
  induction Hvalues; constructor; auto.
  destruct H as [Hkind [Htyped Hlocated]]. split; [exact Hkind |]. split.
  - eapply (proj2 typing_store_extension); eauto.
  - eapply value_locations_monotone; eauto.
Qed.

Lemma call_parameter_inputs_access : forall cenv Sigma L vm m m' params values,
  call_parameter_inputs cenv Sigma L vm m params values ->
  (forall chunk b ofs perm, Mem.valid_access m chunk b ofs perm ->
    Mem.valid_access m' chunk b ofs perm) ->
  call_parameter_inputs cenv Sigma L vm m' params values.
Proof.
  intros cenv Sigma L vm m m' params values Hinputs Haccess.
  induction Hinputs; constructor; auto.
  destruct H as [b [Hget [Hunit | [Hkind [Htyped [Hloc Hfree]]]]]];
    exists b; split; [exact Hget | | exact Hget |].
  - left; exact Hunit.
  - right. split; [exact Hkind |]. split; [exact Htyped |].
    split; [exact Hloc |]. apply Haccess; exact Hfree.
Qed.

Lemma allocated_call_parameter_inputs :
  forall bge AllocSigma vm m params callee allocated AllocSigma' cenv Sigma L values,
  alloc_variables bge AllocSigma vm m params callee allocated AllocSigma' ->
  NoDup (map fst params) ->
  call_parameter_values cenv Sigma L params values ->
  call_parameter_inputs cenv Sigma L callee allocated params values.
Proof.
  intros bge AllocSigma vm m params callee allocated AllocSigma' cenv Sigma L values
    Halloc Hnames Hvalues.
  assert (Hbuild : forall ps vs,
    call_parameter_values cenv Sigma L ps vs ->
    (forall param, In param ps -> In param params) ->
    call_parameter_inputs cenv Sigma L callee allocated ps vs).
  { intros ps vs Hfacts. induction Hfacts; intros Hincluded; constructor.
    - destruct x as [id ty]. destruct H as [Hkind [Htyped Hloc]]. simpl in *.
      destruct (allocated_parameter_chunk_access _ _ _ _ _ _ _ _ Halloc Hnames
        id ty (Hincluded _ (or_introl eq_refl))) as [b [Hget Haccess]].
      exists b. split; [exact Hget |]. destruct Hkind as [Hunit | Hscalar].
      + subst ty. inversion Htyped; subst. left; split; reflexivity.
      + right. split; [exact Hscalar |]. split; [exact Htyped |].
        split; [exact Hloc |]. apply Haccess.
        rewrite (scalar_parameter_chunk_size bge.(genv_cenv) _ Hscalar). lia.
    - apply IHHfacts. intros param Hin. apply Hincluded. right; exact Hin. }
  apply Hbuild; [exact Hvalues | auto].
Qed.

Print Assumptions typed_located_call_arguments.
Print Assumptions allocated_call_parameter_inputs.
