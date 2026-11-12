(* Aggregate array reads return initialized subobject descriptors, rather than
   attempting an impossible scalar load of the aggregate itself. *)
Require Import List ZArith Lia AST Maps Memory Ctypes Integers Errors Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_soundness_arrays BeePL_soundness_fields BeePL_aggregate_memory.
Require Import BeePL_object_coverage BeePL_aggregate_array_elements.
Import ListNotations.
Local Open Scope Z_scope.

Definition aggregate_array_result ge base elem n :=
  Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)).

Theorem aggregate_array_read_progress :
  forall ge Gamma Sigma objects cells p vm m b base elem len attr n ef,
  initialized_object_memory ge Sigma m objects cells -> objects b base (Atype elem len attr) ->
  is_aggregate_type elem = true ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  let result := aggregate_array_result ge base elem n in
  let objects' := add_aggregate_descriptor objects b result elem in
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem)
    m vm (Val (Vloc b result) elem) /\
  initialized_object_memory ge Sigma m objects' cells /\
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc b result) elem) ef elem /\
  runtime_locations (descriptor_heap_locations ge cells objects') (Val (Vloc b result) elem).
Proof.
  intros ge Gamma Sigma objects cells p vm m b base elem len attr n ef
    Hmemory Hobject Hkind Htyped. cbn zeta. unfold aggregate_array_result.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hindex]. subst ef.
  destruct (initialized_aggregate_array_element ge Sigma Gamma m objects cells b base elem len attr n
    Hmemory Hobject Hindex Hkind) as [Hraw [Hpath [Hoffset [Hstate [Hvalue [Hlocations Hreadable]]]]]].
  split; [eapply ssem_array_read_aggregate; eauto; lia |].
  split; [exact Hstate |]. split; assumption.
Qed.

Theorem aggregate_array_read_preservation :
  forall ge Gamma Sigma objects cells p vm m b base elem len attr n ef m' vm' e',
  initialized_object_memory ge Sigma m objects cells -> objects b base (Atype elem len attr) ->
  is_aggregate_type elem = true ->
  type_expr ge.(genv_cenv) Gamma Sigma
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) m' vm' e' ->
  let result := aggregate_array_result ge base elem n in
  let objects' := add_aggregate_descriptor objects b result elem in
  m' = m /\ vm' = vm /\ e' = Val (Vloc b result) elem /\
  initialized_object_memory ge Sigma m' objects' cells /\
  type_expr ge.(genv_cenv) Gamma Sigma e' ef elem /\
  runtime_locations (descriptor_heap_locations ge cells objects') e'.
Proof.
  intros ge Gamma Sigma objects cells p vm m b base elem len attr n ef m' vm' e'
    Hmemory Hobject Hkind Htyped Hstep. cbn zeta. unfold aggregate_array_result.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyped) as [Heffect Hindex]. subst ef.
  destruct (initialized_aggregate_array_element ge Sigma Gamma m objects cells b base elem len attr n
    Hmemory Hobject Hindex Hkind) as [Hraw [Hpath [Hoffset [Hstate [Hvalue [Hlocations Hreadable]]]]]].
  inversion Hstep; subst; try discriminate Hkind.
  - exfalso. eapply value_has_no_small_step; eauto.
  - exfalso. eapply aggregate_full_deref_impossible;
      [exact Hkind | eassumption].
  - split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [exact Hstate |]. split; assumption.
Qed.

Theorem named_aggregate_array_read_progress :
  forall ge Gamma Sigma objects cells p vm m name b elem len attr n ef,
  initialized_object_memory ge Sigma m objects cells -> objects b Ptrofs.zero (Atype elem len attr) ->
  variable_location ge vm name (Atype elem len attr) b -> is_aggregate_type elem = true ->
  type_expr ge.(genv_cenv) Gamma Sigma (Aaccess name (Atype elem len attr) n elem) ef elem ->
  let result := Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem) in
  let objects' := add_aggregate_descriptor objects b result elem in
  ssem_expr ge p vm m (Aaccess name (Atype elem len attr) n elem)
    m vm (Val (Vloc b result) elem) /\
  initialized_object_memory ge Sigma m objects' cells /\
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc b result) elem) ef elem /\
  runtime_locations (descriptor_heap_locations ge cells objects') (Val (Vloc b result) elem).
Proof.
  intros ge Gamma Sigma objects cells p vm m name b elem len attr n ef
    Hmemory Hobject Hbinding Hkind Htyped. cbn zeta.
  destruct (named_array_read_typing _ _ _ _ _ _ _ _ _ Htyped) as [Heffect [Hlookup Hindex]]. subst ef.
  destruct (initialized_aggregate_array_element ge Sigma Gamma m objects cells b Ptrofs.zero elem len attr n
    Hmemory Hobject Hindex Hkind) as [Hraw [Hpath [Hoffset [Hstate [Hvalue [Hlocations Hreadable]]]]]].
  rewrite Ptrofs.add_zero_l in Hstate, Hvalue, Hlocations, Hreadable.
  rewrite Ptrofs.unsigned_zero in Hraw.
  split.
  - destruct Hbinding as [Hlocal | [Hshadow Hglobal]].
    + eapply ssem_array_access_aggregate; eauto; lia.
    + eapply ssem_array_access_global_aggregate; eauto; lia.
  - split; [exact Hstate |]. split; assumption.
Qed.

Lemma named_aggregate_array_step :
  forall ge p vm m name b elem len attr n m' vm' e',
  variable_location ge vm name (Atype elem len attr) b -> is_aggregate_type elem = true ->
  ssem_expr ge p vm m (Aaccess name (Atype elem len attr) n elem) m' vm' e' ->
  m' = m /\ vm' = vm /\
  e' = Val (Vloc b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem.
Proof.
  intros ge p vm m name b elem len attr n m' vm' e' Hbinding Hkind Hstep.
  inversion Hstep; subst; try discriminate Hkind;
    try solve [exfalso; eapply aggregate_full_deref_impossible;
      [exact Hkind | eassumption]].
  all: match goal with
    | H : PTree.get ?key ?vars = Some (?actual, _) |- _ =>
      assert (actual = b) by
        (eapply variable_location_deterministic; [left; exact H | exact Hbinding]); subst actual
    | Hnone : PTree.get ?key ?vars = None, Hsym : Genv.find_symbol ?env ?key = Some ?actual |- _ =>
      assert (actual = b) by
        (eapply variable_location_deterministic; [right; split; eassumption | exact Hbinding]); subst actual
    end.
  all: repeat split; reflexivity.
Qed.

Theorem named_aggregate_array_read_preservation :
  forall ge Gamma Sigma objects cells p vm m name b elem len attr n ef m' vm' e',
  initialized_object_memory ge Sigma m objects cells -> objects b Ptrofs.zero (Atype elem len attr) ->
  variable_location ge vm name (Atype elem len attr) b -> is_aggregate_type elem = true ->
  type_expr ge.(genv_cenv) Gamma Sigma (Aaccess name (Atype elem len attr) n elem) ef elem ->
  ssem_expr ge p vm m (Aaccess name (Atype elem len attr) n elem) m' vm' e' ->
  let result := Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem) in
  let objects' := add_aggregate_descriptor objects b result elem in
  m' = m /\ vm' = vm /\ e' = Val (Vloc b result) elem /\
  initialized_object_memory ge Sigma m' objects' cells /\
  type_expr ge.(genv_cenv) Gamma Sigma e' ef elem /\
  runtime_locations (descriptor_heap_locations ge cells objects') e'.
Proof.
  intros ge Gamma Sigma objects cells p vm m name b elem len attr n ef m' vm' e'
    Hmemory Hobject Hbinding Hkind Htyped Hstep. cbn zeta.
  destruct (named_aggregate_array_step _ _ _ _ _ _ _ _ _ _ _ _ _ Hbinding Hkind Hstep)
    as [Hm [Hvm He]]. subst m' vm' e'.
  destruct (named_aggregate_array_read_progress ge Gamma Sigma objects cells p vm m name b elem len attr n ef
    Hmemory Hobject Hbinding Hkind Htyped) as [_ [Hstate [Hvalue Hlocations]]].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Hstate |]. split; assumption.
Qed.

Print Assumptions aggregate_array_read_progress.
Print Assumptions aggregate_array_read_preservation.
Print Assumptions named_aggregate_array_read_progress.
Print Assumptions named_aggregate_array_read_preservation.
