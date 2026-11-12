(* The actual program builder rules out incomplete composite members. This
   discharges unit/function field cases rather than inventing memory payloads. *)
Require Import List Bool ZArith Integers AST Maps Memory Ctypes Coqlib Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem.
Require Import BeePL_layout_proofs BeePL_object_paths.
Import ListNotations.

Lemma complete_source_member_lookup : forall env members field ty,
  bcomplete_members env members = true ->
  source_member_type field members = OK ty ->
  bcomplete_type env ty = true.
Proof.
  intros env members. induction members as [|member rest IH]; intros field ty Hcomplete Hlookup;
    [discriminate |].
  simpl in Hcomplete. apply andb_true_iff in Hcomplete as [Hhead Htail].
  destruct member as [name t | name sz sg attr width padding]; simpl in Hlookup;
    destruct (ident_eq field name); inversion Hlookup; subst; eauto.
Qed.

Theorem program_source_members_complete : forall p sid co,
  PTree.get sid p.(prog_comp_env) = Some co ->
  bcomplete_members p.(prog_comp_env) co.(co_members) = true.
Proof.
  intros p sid co Hco.
  pose proof (program_composites_consistent p sid co Hco) as Hconsistent.
  pose proof (Ctypes.co_consistent_complete _ _ Hconsistent) as Hcomplete.
  change (Ctypes.complete_members (bcomposite_composite_env p.(prog_comp_env))
    (bmembers_cmembers co.(co_members)) = true) in Hcomplete.
  rewrite translated_members_complete in Hcomplete.
  - exact Hcomplete.
  - eapply built_source_bytes_present. apply prog_comp_env_eq.
Qed.

Theorem program_source_member_complete : forall p sid co field ty,
  PTree.get sid p.(prog_comp_env) = Some co ->
  source_member_type field co.(co_members) = OK ty ->
  bcomplete_type p.(prog_comp_env) ty = true.
Proof.
  intros. eapply complete_source_member_lookup; [|eassumption].
  eapply program_source_members_complete; eauto.
Qed.

Theorem program_typed_field_complete : forall p Gamma Sigma e field ty ef,
  type_expr p.(prog_comp_env) Gamma Sigma (Sfield e field ty) ef ty ->
  bcomplete_type p.(prog_comp_env) ty = true.
Proof.
  intros p Gamma Sigma e field ty ef Htyped. inversion Htyped; subst.
  eapply program_source_member_complete; eauto.
Qed.

Corollary program_unit_field_untypable : forall p Gamma Sigma e field ef,
  ~ type_expr p.(prog_comp_env) Gamma Sigma (Sfield e field Utype) ef Utype.
Proof. intros p Gamma Sigma e field ef Htyped.
  pose proof (program_typed_field_complete _ _ _ _ _ _ _ Htyped). discriminate. Qed.

Theorem program_object_path_complete : forall p root delta ty,
  bcomplete_type p.(prog_comp_env) root = true ->
  object_path p.(prog_comp_env) root delta ty ->
  bcomplete_type p.(prog_comp_env) ty = true.
Proof.
  intros p root delta ty Hcomplete Hpath. induction Hpath.
  - exact Hcomplete.
  - eapply program_source_member_complete; eauto.
  - exact IHHpath.
Qed.

Corollary program_structure_path_not_unit : forall p sid attr co delta,
  PTree.get sid p.(prog_comp_env) = Some co ->
  ~ object_path p.(prog_comp_env) (Stype sid attr) delta Utype.
Proof.
  intros p sid attr co delta Hco Hpath.
  assert (Hcomplete : bcomplete_type p.(prog_comp_env) (Stype sid attr) = true)
    by (simpl; rewrite Hco; reflexivity).
  pose proof (program_object_path_complete _ _ _ _ Hcomplete Hpath). discriminate.
Qed.

Print Assumptions program_typed_field_complete.
Print Assumptions program_unit_field_untypable.
Print Assumptions program_object_path_complete.
Print Assumptions program_structure_path_not_unit.
