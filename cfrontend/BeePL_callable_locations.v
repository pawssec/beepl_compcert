(* Code addresses are certified by the global environment, independently of
   mutable heap typing. This certifies resolution and signatures only: body
   typing and supported call signatures require a separate code contract. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_runtime_locations BeePL_soundness_arrays.

Definition internal_code_locations (bge : genv) : location_context :=
  fun b ofs ty => ofs = Ptrofs.zero /\
    exists args effects result variadic fn,
      ty = Ftype args effects result variadic /\
      Genv.find_funct bge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) /\
      type_of_function fn = Ftype args effects result variadic.

Definition callable_heap_locations (bge : genv) (layout : scalar_layout)
    : location_context :=
  fun b ofs ty =>
    match ty with
    | Ftype _ _ _ _ => internal_code_locations bge b ofs ty
    | _ => array_heap_locations bge.(genv_cenv) layout b ofs ty
    end.

Lemma typed_function_value_canonical :
  forall cenv Gamma Sigma v annotation ef args effects result variadic,
  type_expr cenv Gamma Sigma (Val v annotation) ef
    (Ftype args effects result variadic) ->
  ef = nil /\ annotation = Ftype args effects result variadic /\
    exists b, v = Vloc b Ptrofs.zero.
Proof.
  intros cenv Gamma Sigma v annotation ef args effects result variadic Htyped.
  inversion Htyped; subst. repeat split; eauto.
Qed.

Theorem located_function_value :
  forall bge Gamma Sigma layout v annotation ef args effects result variadic,
  type_expr bge.(genv_cenv) Gamma Sigma (Val v annotation) ef
    (Ftype args effects result variadic) ->
  runtime_locations (callable_heap_locations bge layout) (Val v annotation) ->
  exists b fn,
    v = Vloc b Ptrofs.zero /\
    annotation = Ftype args effects result variadic /\ ef = nil /\
    Genv.find_funct bge (trans_bvalue_cvalue v) = Some (Internal fn) /\
    type_of_function fn = Ftype args effects result variadic.
Proof.
  intros bge Gamma Sigma layout v annotation ef args effects result variadic Htyped Hlocated.
  destruct (typed_function_value_canonical _ _ _ _ _ _ _ _ _ _ Htyped)
    as [Hef [Hannotation [b Hv]]]. subst ef annotation v.
  change (internal_code_locations bge b Ptrofs.zero
    (Ftype args effects result variadic)) in Hlocated.
  destruct Hlocated as [Hofs [args' [effects' [result' [variadic' [fn [Heq [Hfind Hsignature]]]]]]]].
  inversion Heq; subst. exists b, fn. repeat split; assumption || reflexivity.
Qed.

Lemma array_heap_locations_not_function : forall cenv layout b ofs args effects result variadic,
  ~ array_heap_locations cenv layout b ofs (Ftype args effects result variadic).
Proof.
  intros cenv layout b ofs args effects result variadic [Href | Harray].
  - destruct Href as [pt [chunk [Heq Hcell]]]. discriminate.
  - destruct Harray as [elem [len [a [Heq Hrest]]]]. discriminate.
Qed.

Lemma array_heap_locations_callable_embedding : forall bge layout,
  location_context_includes (array_heap_locations bge.(genv_cenv) layout)
    (callable_heap_locations bge layout).
Proof.
  intros bge layout b ofs ty Hlocation. destruct ty; simpl; try exact Hlocation.
  exfalso. eapply array_heap_locations_not_function; exact Hlocation.
Qed.

Lemma callable_heap_locations_monotone : forall bge layout layout',
  (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) ->
  location_context_includes (callable_heap_locations bge layout)
    (callable_heap_locations bge layout').
Proof.
  intros bge layout layout' Hinc b ofs ty Hlocation.
  destruct ty; simpl in *; try exact Hlocation;
    eapply array_heap_locations_monotone; eauto.
Qed.

Print Assumptions typed_function_value_canonical.
Print Assumptions located_function_value.
Print Assumptions array_heap_locations_callable_embedding.
Print Assumptions callable_heap_locations_monotone.
