(* Internal code parameters are immutable aliases; every allocated data
   parameter must satisfy the same storage contract as source initializers.
   This is a necessary admission check, not a parameter initialization proof. *)
Require Import List Bool AST BeeTypes BeePL BeePL_storage_types.
Import ListNotations.

Definition parameter_storage_check (env : bcomposite_env) (ty : type) : bool :=
  is_funtype ty || storage_type_check env ty.

Definition parameters_storage_check (env : bcomposite_env)
    (params : list (ident * type)) : bool :=
  forallb (fun param => parameter_storage_check env (snd param)) params.

Lemma parameter_storage_check_spec : forall env ty,
  parameter_storage_check env ty = true <->
  is_funtype ty = true \/ storage_type_check env ty = true.
Proof. intros; unfold parameter_storage_check; apply orb_true_iff. Qed.

Lemma parameters_storage_check_spec : forall env params,
  parameters_storage_check env params = true <->
  Forall (fun param => is_funtype (snd param) = true \/
    storage_type_check env (snd param) = true) params.
Proof.
  intros env params. unfold parameters_storage_check.
  rewrite forallb_forall, Forall_forall.
  split; intros H param Hin; apply parameter_storage_check_spec; auto.
Qed.

Lemma parameters_storage_member : forall env params id ty,
  parameters_storage_check env params = true -> In (id,ty) params ->
  parameter_storage_check env ty = true.
Proof.
  intros env params id ty H Hin. unfold parameters_storage_check in H.
  rewrite forallb_forall in H. exact (H (id,ty) Hin).
Qed.

Lemma parameter_storage_data : forall env ty,
  parameter_storage_check env ty = true -> is_funtype ty = false ->
  storage_type_check env ty = true.
Proof. intros env ty H Hdata. unfold parameter_storage_check in H. rewrite Hdata in H; exact H. Qed.

Lemma parameters_storage_data_member : forall env params id ty,
  parameters_storage_check env params = true -> In (id,ty) params ->
  is_funtype ty = false -> storage_type_check env ty = true.
Proof. intros. eapply parameter_storage_data; eauto using parameters_storage_member. Qed.

Lemma parameters_storage_restrict : forall env params selected,
  parameters_storage_check env params = true -> incl selected params ->
  parameters_storage_check env selected = true.
Proof.
  intros env params selected H Hincl. unfold parameters_storage_check in *.
  rewrite forallb_forall in *. intros param Hin. apply H, Hincl, Hin.
Qed.

Lemma parameters_storage_data_list : forall env params selected,
  parameters_storage_check env params = true -> incl selected params ->
  Forall (fun param => is_funtype (snd param) = false) selected ->
  Forall (fun param => storage_type_check env (snd param) = true) selected.
Proof.
  intros env params selected H Hsub Hdata. rewrite Forall_forall in *.
  intros [id ty] Hin. eapply parameters_storage_data_member; eauto.
Qed.

Lemma parameter_storage_function : forall env args effects result variadic,
  parameter_storage_check env (Ftype args effects result variadic) = true.
Proof. reflexivity. Qed.

Lemma parameter_storage_existing_data : forall env ty,
  storage_type_check env ty = true -> parameter_storage_check env ty = true.
Proof. intros; apply parameter_storage_check_spec; auto. Qed.

Print Assumptions parameters_storage_check_spec.
Print Assumptions parameters_storage_data_list.
