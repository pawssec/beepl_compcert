(* Public entry point for source type soundness.

   The previous five admitted claims have been retired, not proved from an
   impossible precondition. BeePL_legacy_soundness_audit establishes why the
   old store_well_typed premise and normalization/effect claims were unsuitable.
   The exported results use the initialized, coherent program configuration,
   allow allocation to extend the store, and prove safety of actual executions.
   They do not assert termination, compiler correctness, or kernel adequacy.

   Main APIs:
     program_expression_progress_checked
     program_expression_preservation_checked
     program_closure_preservation / program_closures_preservation
     program_closure_normal_form_is_typed_value
     program_reaches_cannot_get_stuck
     program_closures_values_or_progress

   Historical consumers of progress_ssem_expr_exprs and fixed-store preservation
   must migrate to these corrected statements. In particular BeePL_ebpf_proofs.v
   is unfinished separate work and is not part of the checked soundness API.
 *)
Require Import List Bool Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_store.
Require Export BeePL_program_soundness_assembly BeePL_program_multistep.
From mathcomp Require Import all_ssreflect.

(* Retained checked helper results. The first one audits a limitation of the
   legacy variable invariant; it is not used in the new soundness proof. *)
Lemma legacy_structure_variable_impossible : forall Gamma Sigma bge vm m x id attr,
  PTree.get x Gamma = Some (Stype id attr) ->
  ~ well_formed_var Gamma Sigma bge vm m.
Proof.
  intros Gamma Sigma bge vm m x id attr Hentry Hvars.
  inversion Hvars as [Hlocal | Hglobal]; subst.
  - destruct (Hlocal x (Stype id attr) Hentry)
      as [b [t [v [Hlookup [Heq [Hstore Hread]]]]]].
    inversion Hread; subst; discriminate.
  - destruct (Hglobal x (Stype id attr) Hentry)
      as [b [v [Hmissing [Hsymbol [Hstore Hread]]]]].
    inversion Hread; subst; discriminate.
Qed.

Lemma evaluated_arguments_identity : forall bge p vm m es,
  is_values es -> ssem_exprs bge p vm m es m vm es.
Proof.
  intros bge p vm m es. induction es as [|e es IH]; simpl; intro Hvalues.
  - constructor.
  - move/andP: Hvalues => [Hhead Htail].
    destruct e; simpl in Hhead; try discriminate.
    apply ssem_cons2. apply IH. exact Htail.
Qed.

Lemma callable_value_is_location : forall cenv Gamma Sigma v annotation ef te args effects result variadic,
  type_expr cenv Gamma Sigma (Val v annotation) ef te ->
  eq_type te (Ptrtype (Fptype args effects result variadic)) ||
    eq_type te (Ftype args effects result variadic) ->
  exists b ofs, v = Vloc b ofs.
Proof.
  intros cenv Gamma Sigma v annotation ef te args effects result variadic Htyped Hfun.
  inversion Htyped; subst; simpl in Hfun; try discriminate; eauto.
Qed.

Lemma subst_preservation : forall cenv Gamma Sigma x t v e ef t',
  type_expr cenv (extend_context Gamma x t) Sigma e ef t' ->
  type_expr cenv Gamma Sigma (Val v t) nil t ->
  type_expr cenv Gamma Sigma (subst x (Val v t) e) ef t'.
Proof.
  intros. eapply value_substitution_preserves_typing; eauto.
Qed.

Lemma well_typed_val_expr : forall cenv Gamma Sigma layout v t chunk m l ofs,
  typed_memory_layout cenv Sigma layout m ->
  layout l ofs t chunk ->
  deref_addr t m l ofs Full v ->
  type_expr cenv Gamma Sigma (Val v t) nil t.
Proof.
  intros cenv Gamma Sigma layout v t chunk m l ofs Hmemory Hentry Hread.
  eapply typed_memory_cell_read_preservation; eauto.
Qed.

Print Assumptions program_expression_progress_checked.
Print Assumptions program_expression_preservation_checked.
Print Assumptions program_closure_preservation.
Print Assumptions program_closure_normal_form_is_typed_value.
Print Assumptions program_reaches_cannot_get_stuck.
Print Assumptions subst_preservation.
Print Assumptions well_typed_val_expr.
