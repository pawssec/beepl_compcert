(* Evaluation-context cases consume the recursive child/list preservation
   hypothesis. Suspended expressions keep typing, locations and captured maps. *)
Require Import List Bool Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_auxlemmas BeePL_runtime_locations.
Require Import BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_aggregate_memory BeePL_initialized_runtime BeePL_initialized_lists.
Require Import BeePL_callable_entry.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Theorem initialized_application_function_context :
  forall ge Gamma Sigma vm m objects cells packets p fn es rt fty variadic args call_effects ef efs
    Sigma' vm' m' objects' cells' packets' fn' ef',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (App fn es rt) (ef ++ call_effects ++ efs) rt ->
  type_expr ge.(genv_cenv) Gamma Sigma fn ef fty ->
  (eq_type fty (Ptrtype (Fptype args call_effects rt variadic)) ||
    eq_type fty (Ftype args call_effects rt variadic)) = true ->
  type_exprs ge.(genv_cenv) Gamma Sigma es efs args ->
  ssem_expr ge p vm m fn m' vm' fn' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' fn' ef' fty ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (App fn es rt) m' vm' (App fn' es rt) /\
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (App fn' es rt) (ef' ++ call_effects ++ efs) rt /\
  sub_effect (ef' ++ call_effects ++ efs) (ef ++ call_effects ++ efs) = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p fn es rt fty variadic args call_effects ef efs
    Sigma' vm' m' objects' cells' packets' fn' ef'
    [Hheap Htyped [Hfnloc Hesloc] [Hfnframes Hesframes]] Hfn Hsignature Hes Hstep
    Hupdate [Hheap' Hfn' Hfnloc' Hfnframes'] Hsub.
  destruct Hupdate as [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents].
  split; [apply ssem_app1; exact Hstep |]. split.
  - constructor.
    + exact Hheap'.
    + eapply ty_app; [exact Hfn' |exact Hsignature |]. eapply (proj1 typing_store_extension); eauto.
    + split; [exact Hfnloc' |]. rewrite all_expr_locations_Forall, Forall_forall in *.
      intros e Hin. eapply runtime_locations_monotone; [|apply Hesloc; exact Hin].
      apply packet_heap_locations_monotone; assumption.
    + split; [exact Hfnframes' |]. rewrite all_expr_locations_Forall, Forall_forall in *.
      intros e Hin. eapply initialized_runtime_frames_evolve; eauto.
  - apply sub_effect_concat; [exact Hsub |apply sub_effect_refl].
Qed.

Theorem initialized_application_arguments_context :
  forall ge Gamma Sigma vm m objects cells packets p b base fty args call_effects rt variadic es efs
    Sigma' vm' m' objects' cells' packets' es' efs',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (App (Val (Vloc b base) fty) es rt) (call_effects ++ efs) rt ->
  type_expr ge.(genv_cenv) Gamma Sigma (Val (Vloc b base) fty) [] fty ->
  (eq_type fty (Ptrtype (Fptype args call_effects rt variadic)) ||
    eq_type fty (Ftype args call_effects rt variadic)) = true ->
  is_values es = false ->
  ssem_exprs ge p vm m es m' vm' es' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_list_configuration ge Gamma Sigma' vm' m' objects' cells' packets' es' efs' args ->
  sub_effect efs' efs = true ->
  ssem_expr ge p vm m (App (Val (Vloc b base) fty) es rt) m' vm' (App (Val (Vloc b base) fty) es' rt) /\
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets'
    (App (Val (Vloc b base) fty) es' rt) (call_effects ++ efs') rt /\
  sub_effect (call_effects ++ efs') (call_effects ++ efs) = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base fty args call_effects rt variadic es efs
    Sigma' vm' m' objects' cells' packets' es' efs'
    [Hheap Htyped [Hfnloc Hesloc] [Hfnframes Hesframes]] Hfn Hsignature Hnonvalues Hstep Hupdate
    [Hheap' Hes' Hesloc' Hesframes'] Hsub.
  destruct Hupdate as [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents].
  split; [apply ssem_app2; assumption |]. split.
  - constructor.
    + exact Hheap'.
    + change (call_effects ++ efs') with ([] ++ call_effects ++ efs').
      eapply ty_app; [|exact Hsignature |exact Hes']. eapply (proj2 typing_store_extension); eauto.
    + split; [|exact Hesloc']. eapply value_locations_monotone; [|exact Hfnloc].
      apply packet_heap_locations_monotone; assumption.
    + split; [exact I |exact Hesframes'].
  - apply sub_effect_concat; [apply sub_effect_refl |exact Hsub].
Qed.

Theorem initialized_structure_arguments_context :
  forall ge Gamma Sigma vm m objects cells packets p sid ids es result ef types
    Sigma' vm' m' objects' cells' packets' es' ef',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets (Sinit sid ids es result) ef result ->
  type_exprs ge.(genv_cenv) Gamma Sigma es ef types ->
  is_values es = false ->
  ssem_exprs ge p vm m es m' vm' es' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_list_configuration ge Gamma Sigma' vm' m' objects' cells' packets' es' ef' types ->
  sub_effect ef' ef = true ->
  ssem_expr ge p vm m (Sinit sid ids es result) m' vm' (Sinit sid ids es' result) /\
  initialized_runtime_configuration ge Gamma Sigma' vm' m' objects' cells' packets' (Sinit sid ids es' result) ef' result /\
  sub_effect ef' ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p sid ids es result ef types
    Sigma' vm' m' objects' cells' packets' es' ef'
    [Hheap Htyped Hloc Hframes] Hargs Hnonvalues Hstep Hupdate [Hheap' Hargs' Hloc' Hframes'] Hsub.
  split; [apply ssem_sinit1; assumption |]. split; [|exact Hsub]. constructor; try assumption.
  inversion Htyped; subst.
  match goal with Hother : type_exprs _ _ _ es _ ?other |- _ =>
    assert (Heq : other = types) by
      (pose proof (typed_arguments_annotations _ _ _ _ _ _ Hother);
       pose proof (typed_arguments_annotations _ _ _ _ _ _ Hargs); congruence)
  end.
  subst. eapply ty_sinit; eauto.
Qed.

Print Assumptions initialized_application_function_context.
Print Assumptions initialized_application_arguments_context.
Print Assumptions initialized_structure_arguments_context.
