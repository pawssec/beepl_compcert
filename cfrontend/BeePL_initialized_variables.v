(* Variable reads retain arbitrary certified location predicates, including
   references whose targets are initialized aggregate descriptors. Direct
   struct variables remain outside the existing variable binding relation. *)
Require Import List Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_soundness_arrays BeePL_soundness_variables.
Require Import BeePL_function_variables BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_aggregate_memory BeePL_object_coverage.

Theorem located_callable_variable_progress : forall Gamma Sigma bge vm layout L p m x ty,
  location_context_includes (callable_heap_locations bge layout) L ->
  callable_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations L layout m ->
  PTree.get x Gamma = Some ty ->
  exists v, ssem_expr bge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations L (Val v ty).
Proof.
  intros Gamma Sigma bge vm layout L p m x ty Hinc Hvars Hmemory Hstored Hget.
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
      * split; [apply ty_valarray; exact Hsigma|apply Hinc; exact Harray].
    + exists Vunit. split.
      * destruct Hlocation as [Hlocal|[Hnone Hglobal]].
        -- eapply ssem_lvar_unit; exact Hlocal.
        -- eapply ssem_gbvar_unit; eauto.
      * split; [apply ty_valu|exact I].
  - assert (HcodeLocated : L b Ptrofs.zero ty) by (apply Hinc; destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty Hrest]]]]]]]; subst ty; change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)); split; [exact Hofs |]; exists args, effects, result, variadic, fn; auto).
    destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty. exists (Vloc b Ptrofs.zero). split.
    + eapply global_function_variable_progress; eauto.
    + split; [apply ty_valfun|].
      exact HcodeLocated.
  - assert (HcodeLocated : L b Ptrofs.zero ty) by (apply Hinc; destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty Hrest]]]]]]]; subst ty; change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)); split; [exact Hofs |]; exists args, effects, result, variadic, fn; auto).
    destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty. exists (Vloc b Ptrofs.zero). split.
    + eapply local_function_variable_progress; eauto.
    + split; [apply ty_valfun|].
      exact HcodeLocated.
Qed.

Theorem located_callable_variable_preservation : forall Gamma Sigma bge vm layout L p m x ty m' vm' e',
  location_context_includes (callable_heap_locations bge layout) L ->
  callable_variable_layout Gamma Sigma bge vm layout ->
  typed_memory_layout bge.(genv_cenv) Sigma layout m ->
  memory_locations L layout m ->
  PTree.get x Gamma = Some ty ->
  ssem_expr bge p vm m (Var x ty) m' vm' e' ->
  m' = m /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations L e'.
Proof.
  intros Gamma Sigma bge vm layout L p m x ty m' vm' e'
    Hinc Hvars Hmemory Hstored Hget Hstep.
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
        subst b0. do 2 (split; [reflexivity|]). split; [apply ty_valarray; exact Hsigma|apply Hinc; exact Harray].
      * assert (b0 = b) by (eapply variable_location_deterministic; [right; split; eassumption|exact Hlocation]).
        subst b0. do 2 (split; [reflexivity|]). split; [apply ty_valarray; exact Hsigma|apply Hinc; exact Harray].
    + inversion Hstep; subst;
        try solve [exfalso; eapply unit_full_deref_impossible; eauto].
      * do 2 (split; [reflexivity|]). split; [apply ty_valu|exact I].
      * do 2 (split; [reflexivity|]). split; [apply ty_valu|exact I].
  - assert (HcodeLocated : L b Ptrofs.zero ty) by (apply Hinc; destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty Hrest]]]]]]]; subst ty; change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)); split; [exact Hofs |]; exists args, effects, result, variadic, fn; auto).
    destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty.
    destruct (global_function_variable_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hmissing Hsymbol Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'.
    do 2 (split; [reflexivity|]). split; [apply ty_valfun|].
    exact HcodeLocated.
  - assert (HcodeLocated : L b Ptrofs.zero ty) by (apply Hinc; destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty Hrest]]]]]]]; subst ty; change (internal_code_locations bge b Ptrofs.zero (Ftype args effects result variadic)); split; [exact Hofs |]; exists args, effects, result, variadic, fn; auto).
    destruct Hcode as [Hofs [args [effects [result [variadic [fn [Hty [Hfind Hsig]]]]]]]].
    subst ty.
    destruct (local_function_variable_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hlocal Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'.
    do 2 (split; [reflexivity|]). split; [apply ty_valfun|].
    exact HcodeLocated.
Qed.


Theorem initialized_variable_progress : forall Gamma Sigma ge vm cells objects p m x ty,
  callable_variable_layout Gamma Sigma ge vm cells ->
  initialized_object_memory ge Sigma m objects cells ->
  PTree.get x Gamma = Some ty ->
  exists v, ssem_expr ge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr ge.(genv_cenv) Gamma Sigma (Val v ty) nil ty /\
    runtime_locations (descriptor_heap_locations ge cells objects) (Val v ty).
Proof.
  intros Gamma Sigma ge vm cells objects p m x ty Hvars Hmemory Hget.
  destruct Hmemory as [Hobjects Hcoverage Hcells Hlocations HscalarCoherence].
  eapply located_callable_variable_progress; eauto. apply callable_descriptor_embedding.
Qed.

Theorem initialized_variable_preservation :
  forall Gamma Sigma ge vm cells objects p m x ty final vm' e',
  callable_variable_layout Gamma Sigma ge vm cells ->
  initialized_object_memory ge Sigma m objects cells ->
  PTree.get x Gamma = Some ty ->
  ssem_expr ge p vm m (Var x ty) final vm' e' ->
  final = m /\ vm' = vm /\
  initialized_object_memory ge Sigma final objects cells /\
  type_expr ge.(genv_cenv) Gamma Sigma e' nil ty /\
  runtime_locations (descriptor_heap_locations ge cells objects) e'.
Proof.
  intros Gamma Sigma ge vm cells objects p m x ty final vm' e' Hvars Hmemory Hget Hstep.
  destruct (located_callable_variable_preservation Gamma Sigma ge vm cells
    (descriptor_heap_locations ge cells objects) p m x ty final vm' e'
    (callable_descriptor_embedding ge cells objects) Hvars
    (initialized_object_cells _ _ _ _ _ Hmemory)
    (initialized_object_locations _ _ _ _ _ Hmemory) Hget Hstep)
    as [Hm [Hvm [Htype Hlocations]]].
  subst final vm'. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Hmemory |]. split; assumption.
Qed.

Print Assumptions located_callable_variable_progress.
Print Assumptions located_callable_variable_preservation.
Print Assumptions initialized_variable_progress.
Print Assumptions initialized_variable_preservation.
