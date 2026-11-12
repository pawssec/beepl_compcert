(* Variable contexts distinguish initialized data bindings from authentic
   internal function addresses. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_variables.
Require Import BeePL_function_variables BeePL_callable_locations.

Inductive callable_variable_binding (bge : genv) (Sigma : store_context)
    (vm : vmap) (layout : scalar_layout) (x : ident) (ty : type) : Prop :=
| callable_variable_data : forall b,
    variable_location bge vm x ty b ->
    heap_variable_binding bge.(genv_cenv) Sigma layout b ty ->
    is_funtype ty = false ->
    callable_variable_binding bge Sigma vm layout x ty
| callable_variable_code : forall b,
    PTree.get x vm = None -> Genv.find_symbol bge x = Some b ->
    internal_code_locations bge b Ptrofs.zero ty ->
    callable_variable_binding bge Sigma vm layout x ty
| callable_variable_local_code : forall b,
    PTree.get x vm = Some (b, ty) ->
    internal_code_locations bge b Ptrofs.zero ty ->
    callable_variable_binding bge Sigma vm layout x ty.

Definition callable_variable_layout (Gamma : ty_context) (Sigma : store_context)
    (bge : genv) (vm : vmap) (layout : scalar_layout) : Prop :=
  forall x ty, PTree.get x Gamma = Some ty ->
    callable_variable_binding bge Sigma vm layout x ty.

Lemma callable_variable_binding_extend : forall bge Sigma Sigma' vm layout layout' x ty,
  store_context_extends Sigma Sigma' ->
  (forall b ofs t chunk, layout b ofs t chunk -> layout' b ofs t chunk) ->
  callable_variable_binding bge Sigma vm layout x ty ->
  callable_variable_binding bge Sigma' vm layout' x ty.
Proof.
  intros bge Sigma Sigma' vm layout layout' x ty Hext Hinc Hbinding.
  destruct Hbinding.
  - eapply callable_variable_data; [eassumption| |eassumption].
    eapply heap_variable_binding_extend; eauto.
  - eapply callable_variable_code; eauto.
  - eapply callable_variable_local_code; eauto.
Qed.

Lemma callable_variable_layout_extend : forall Gamma Sigma Sigma' bge vm layout layout',
  store_context_extends Sigma Sigma' ->
  (forall b ofs t chunk, layout b ofs t chunk -> layout' b ofs t chunk) ->
  callable_variable_layout Gamma Sigma bge vm layout ->
  callable_variable_layout Gamma Sigma' bge vm layout'.
Proof.
  intros Gamma Sigma Sigma' bge vm layout layout' Hext Hinc Hvars x ty Hget.
  eapply callable_variable_binding_extend; eauto.
Qed.

Theorem callable_variable_progress : forall Gamma Sigma bge vm layout p m x ty,
  callable_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (callable_heap_locations bge layout) layout m ->
  PTree.get x Gamma = Some ty ->
  exists v, ssem_expr bge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations (callable_heap_locations bge layout) (Val v ty).
Proof.
  intros Gamma Sigma bge vm layout p m x ty Hvars Hmemory Hstored Hget.
  destruct (Hvars x ty Hget) as [b Hlocation Hbinding Hnonfun|b Hmissing Hsymbol Hcode|b Hlocal Hcode].
  - destruct Hbinding as [ty chunk Hcell|elem len a Hsigma Harray|].
    + destruct (typed_memory_cell_read bge.(genv_cenv) Gamma Sigma m b Ptrofs.zero
        ty chunk (Hmemory _ _ _ _ Hcell)) as [v [Hread Htyped]].
      exists v. split.
      * destruct Hlocation as [Hlocal|[Hnone Hglobal]].
        -- eapply ssem_lvar; eauto.
        -- eapply ssem_gbvar; eauto.
      * split; [exact Htyped|]. eapply Hstored; eauto.
    + exists (Vloc b Ptrofs.zero). split.
      * destruct Hlocation as [Hlocal|[Hnone Hglobal]].
        -- apply ssem_lvar_array; exact Hlocal.
        -- apply ssem_gbvar_array; assumption.
      * split; [apply ty_valarray; exact Hsigma|exact Harray].
    + exists Vunit. split.
      * destruct Hlocation as [Hlocal|[Hnone Hglobal]].
        -- eapply ssem_lvar_unit; exact Hlocal.
        -- eapply ssem_gbvar_unit; eauto.
      * split; [apply ty_valu|exact I].
  - destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty. exists (Vloc b Ptrofs.zero). split.
    + eapply global_function_variable_progress; eauto.
    + split; [apply ty_valfun|].
      change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)).
      split; [reflexivity|]. exists args, effects, result, variadic, fn.
      repeat split; assumption || reflexivity.
  - destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty. exists (Vloc b Ptrofs.zero). split.
    + eapply local_function_variable_progress; eauto.
    + split; [apply ty_valfun|].
      change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)).
      split; [reflexivity|]. exists args, effects, result, variadic, fn.
      repeat split; assumption || reflexivity.
Qed.

Theorem callable_variable_preservation : forall Gamma Sigma bge vm layout p m x ty m' vm' e',
  callable_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations (callable_heap_locations bge layout) layout m ->
  PTree.get x Gamma = Some ty ->
  ssem_expr bge p vm m (Var x ty) m' vm' e' ->
  m' = m /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations (callable_heap_locations bge layout) e'.
Proof.
  intros Gamma Sigma bge vm layout p m x ty m' vm' e'
    Hvars Hmemory Hstored Hget Hstep.
  destruct (Hvars x ty Hget) as [b Hlocation Hbinding Hnonfun|b Hmissing Hsymbol Hcode|b Hlocal Hcode].
  - destruct Hbinding as [ty chunk Hcell|elem len a Hsigma Harray|].
    + assert (Hmode := typed_cell_access _ _ _ _ _ _ _ (Hmemory _ _ _ _ Hcell)).
      inversion Hstep; subst; try discriminate Hmode; try discriminate Hnonfun.
      * assert (l = b) by (eapply variable_location_deterministic; [left; eassumption|exact Hlocation]).
        subst l. do 2 (split; [reflexivity|]). split.
        -- eapply typed_memory_cell_read_preservation; eauto.
        -- eapply Hstored; eauto.
      * assert (l = b) by (eapply variable_location_deterministic; [right; split; eassumption|exact Hlocation]).
        subst l. do 2 (split; [reflexivity|]). split.
        -- eapply typed_memory_cell_read_preservation; eauto.
        -- eapply Hstored; eauto.
    + inversion Hstep; subst;
        try solve [exfalso; eapply array_full_deref_impossible; eauto].
      * assert (b0 = b) by (eapply variable_location_deterministic; [left; eassumption|exact Hlocation]).
        subst b0. do 2 (split; [reflexivity|]). split; [apply ty_valarray; exact Hsigma|exact Harray].
      * assert (b0 = b) by (eapply variable_location_deterministic; [right; split; eassumption|exact Hlocation]).
        subst b0. do 2 (split; [reflexivity|]). split; [apply ty_valarray; exact Hsigma|exact Harray].
    + inversion Hstep; subst;
        try solve [exfalso; eapply unit_full_deref_impossible; eauto].
      * do 2 (split; [reflexivity|]). split; [apply ty_valu|exact I].
      * do 2 (split; [reflexivity|]). split; [apply ty_valu|exact I].
  - destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty.
    destruct (global_function_variable_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hmissing Hsymbol Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'.
    do 2 (split; [reflexivity|]). split; [apply ty_valfun|].
    change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)).
    split; [reflexivity|]. exists args, effects, result, variadic, fn.
    repeat split; assumption || reflexivity.
  - destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty.
    destruct (local_function_variable_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hlocal Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'.
    do 2 (split; [reflexivity|]). split; [apply ty_valfun|].
    change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)).
    split; [reflexivity|]. exists args, effects, result, variadic, fn.
    repeat split; assumption || reflexivity.
Qed.

Print Assumptions callable_variable_progress.
Print Assumptions callable_variable_preservation.
