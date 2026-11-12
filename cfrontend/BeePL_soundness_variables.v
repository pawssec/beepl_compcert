(* Variable bindings for scalar cells, arrays, and unit values.
   These invariants use the checked heap layout, not legacy well_formed_var. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_soundness_arrays.

Inductive heap_variable_binding (cenv : bcomposite_env) (Sigma : store_context)
    (layout : scalar_layout) (b : Values.block) : type -> Prop :=
| heap_variable_scalar : forall ty chunk,
    layout b Ptrofs.zero ty chunk ->
    heap_variable_binding cenv Sigma layout b ty
| heap_variable_array : forall elem len a,
    object_type_at cenv Sigma b (Ptrofs.unsigned Ptrofs.zero) (Atype elem len a) ->
    array_heap_locations cenv layout b Ptrofs.zero (Atype elem len a) ->
    heap_variable_binding cenv Sigma layout b (Atype elem len a)
| heap_variable_unit : heap_variable_binding cenv Sigma layout b Utype.

Definition mixed_variable_layout (Gamma : ty_context) (Sigma : store_context)
    (bge : genv) (vm : vmap) (layout : scalar_layout) : Prop :=
  forall x ty, PTree.get x Gamma = Some ty ->
  exists b, variable_location bge vm x ty b /\
    heap_variable_binding bge.(genv_cenv) Sigma layout b ty.

Lemma heap_variable_binding_extend : forall cenv Sigma Sigma' layout layout' b ty,
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) ->
  heap_variable_binding cenv Sigma layout b ty ->
  heap_variable_binding cenv Sigma' layout' b ty.
Proof.
  intros cenv Sigma Sigma' layout layout' b ty Hext Hinc Hbinding.
  destruct Hbinding.
  - eapply heap_variable_scalar; eauto.
  - apply heap_variable_array; [eapply object_type_at_store_extension; eauto |].
    eapply array_heap_locations_monotone; eauto.
  - apply heap_variable_unit.
Qed.

Lemma mixed_variable_layout_extend : forall Gamma Sigma Sigma' bge vm layout layout',
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) ->
  mixed_variable_layout Gamma Sigma bge vm layout ->
  mixed_variable_layout Gamma Sigma' bge vm layout'.
Proof.
  intros Gamma Sigma Sigma' bge vm layout layout' Hext Hinc Hvars x ty Hlookup.
  destruct (Hvars _ _ Hlookup) as [b [Hlocation Hbinding]].
  exists b. split; [exact Hlocation |].
  eapply heap_variable_binding_extend; eauto.
Qed.

Theorem mixed_variable_progress : forall Gamma Sigma bge vm layout p m x ty,
  mixed_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  PTree.get x Gamma = Some ty ->
  exists v, ssem_expr bge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) (Val v ty).
Proof.
  intros Gamma Sigma bge vm layout p m x ty Hvars Hmemory Hstored Hlookup.
  destruct (Hvars _ _ Hlookup) as [b [Hlocation Hbinding]].
  destruct Hbinding as [ty chunk Hcell | elem len a Hstore Harray |].
  - destruct (typed_memory_cell_read bge.(genv_cenv) Gamma Sigma m b Ptrofs.zero
      ty chunk (Hmemory _ _ _ _ Hcell)) as [v [Hread Htyped]].
    exists v. split.
    + destruct Hlocation as [Hlocal | [Hmissing Hglobal]].
      * eapply ssem_lvar; eauto.
      * eapply ssem_gbvar; eauto.
    + split; [exact Htyped |]. eapply Hstored; eauto.
  - exists (Vloc b Ptrofs.zero). split.
    + destruct Hlocation as [Hlocal | [Hmissing Hglobal]].
      * apply ssem_lvar_array; exact Hlocal.
      * apply ssem_gbvar_array; assumption.
    + split; [apply ty_valarray; exact Hstore | exact Harray].
  - exists Vunit. split.
    + destruct Hlocation as [Hlocal | [Hmissing Hglobal]].
      * eapply ssem_lvar_unit; exact Hlocal.
      * eapply ssem_gbvar_unit; eauto.
    + split; [apply ty_valu|exact I].
Qed.

Lemma unit_full_deref_impossible : forall m b ofs v,
  ~ deref_addr Utype m b ofs Full v.
Proof. intros m b ofs v Hread. inversion Hread; subst; discriminate. Qed.

Theorem mixed_variable_preservation : forall Gamma Sigma bge vm layout p m x ty m' vm' e',
  mixed_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m ->
  PTree.get x Gamma = Some ty ->
  ssem_expr bge p vm m (Var x ty) m' vm' e' ->
  m' = m /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) e'.
Proof.
  intros Gamma Sigma bge vm layout p m x ty m' vm' e' Hvars Hmemory Hstored Hlookup Hstep.
  destruct (Hvars _ _ Hlookup) as [b [Hlocation Hbinding]].
  destruct Hbinding as [ty chunk Hcell | elem len a Hstore Harray |].
  - assert (Hmode := typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)).
    inversion Hstep; subst; try discriminate Hmode.
    + assert (l = b).
      { eapply variable_location_deterministic; [left; eassumption | exact Hlocation]. }
      subst l. do 2 (split; [reflexivity |]). split.
      * eapply typed_memory_cell_read_preservation; eauto.
      * eapply Hstored; eauto.
    + assert (l = b).
      { eapply variable_location_deterministic; [right; split; eassumption | exact Hlocation]. }
      subst l. do 2 (split; [reflexivity |]). split.
      * eapply typed_memory_cell_read_preservation; eauto.
      * eapply Hstored; eauto.
  - inversion Hstep; subst;
      try solve [exfalso; eapply array_full_deref_impossible; eauto].
    + assert (b0 = b).
      { eapply variable_location_deterministic; [left; eassumption | exact Hlocation]. }
      subst b0. do 2 (split; [reflexivity |]). split;
        [apply ty_valarray; exact Hstore | exact Harray].
    + assert (b0 = b).
      { eapply variable_location_deterministic; [right; split; eassumption | exact Hlocation]. }
      subst b0. do 2 (split; [reflexivity |]). split;
        [apply ty_valarray; exact Hstore | exact Harray].
  - inversion Hstep; subst;
      try solve [exfalso; eapply unit_full_deref_impossible; eauto].
    all: do 2 (split; [reflexivity|]); split; [apply ty_valu|exact I].
Qed.

Print Assumptions mixed_variable_progress.
Print Assumptions mixed_variable_preservation.
