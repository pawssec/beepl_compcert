(* Initial-state adequacy for programs with no data globals.  BeePL's source
   semantics has no initial_state relation: this module uses the real CompCert
   loader, while keeping source-body well-formedness explicit. *)
Require Import Coqlib List ZArith Integers AST Maps Memory Ctypes Globalenvs Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_code_contracts BeePL_callable_variables BeePL_callable_locations.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_layout_coherence.
Require Import BeePL_packet_state BeePL_packet_heap BeePL_packet_coverage BeePL_packet_object_layout.
Require Import BeePL_packet_bindings BeePL_heap_extents BeePL_block_extents.
Require Import BeePL_frame_free BeePL_initialized_runtime BeePL_coherent_configurations BeePL_program_runtime.
Import ListNotations.

Definition initial_no_objects : aggregate_object_context := fun _ _ _ => False.
Definition initial_no_cells : scalar_layout := fun _ _ _ _ => False.
Definition initial_no_packets : packet_locations := fun _ _ => False.
Definition source_globals (p : program) : ty_context :=
  bind_globdef empty_context (AST.prog_defs (trans_program_astprog p)).

Lemma typed_global_member : forall efenv cenv Gamma Sigma defs fd,
  type_globdefs efenv cenv Gamma Sigma defs -> In fd defs ->
  type_globdef efenv cenv Gamma Sigma fd.
Proof. intros * H; induction H; simpl; intros Hin; [contradiction|].
  destruct Hin; subst; auto. Qed.

Theorem typed_program_internal_code : forall p,
  type_program p -> internal_code_contract (globalenv p) (source_globals p) empty_stcontext.
Proof.
  intros p Hprogram b fn Hfind.
  change (Genv.find_funct (Genv.globalenv (trans_program_astprog p))
    (Values.Vptr b Ptrofs.zero) = Some (Internal fn)) in Hfind.
  rewrite Genv.find_funct_find_funct_ptr in Hfind.
  destruct (Genv.find_funct_ptr_inversion _ _ Hfind) as [id Hin].
  inversion Hprogram; subst.
  assert (Hmember : In (Gfun (Internal fn))
    (map (fun '(_, gd, _) => gd) (prog_defs p))).
  { unfold trans_program_astprog in Hin; simpl in Hin.
    apply in_map_iff in Hin. destruct Hin as [[[name gd] section] [Heq Hin]].
    inversion Heq; subst. apply in_map_iff. exists (id, Gfun (Internal fn), section). split; [reflexivity|exact Hin]. }
  match goal with Hdefs : type_globdefs _ _ _ _ _ |- _ =>
    pose proof (typed_global_member _ _ _ _ _ _ Hdefs Hmember) as Htyped end.
  inversion Htyped; subst; try discriminate.
  match goal with Hfd : type_fundef _ _ _ _ _ |- _ => inversion Hfd; subst end;
    try assumption; try discriminate.
  match goal with H : Gfun (Internal _) = Gfun (Internal _) |- _ => inversion H; subst end.
  assumption.
Qed.

Definition resolved_internal_globals (ge : genv) (Gamma : ty_context) : Prop := forall id ty,
  Gamma ! id = Some ty -> exists b fn,
    Genv.find_symbol ge id = Some b /\
    Genv.find_funct ge (Values.Vptr b Ptrofs.zero) = Some (Internal fn) /\
    ty = type_of_function fn.

Lemma initial_code_bindings : forall ge Gamma,
  resolved_internal_globals ge Gamma ->
  packet_variable_layout Gamma empty_stcontext ge empty_vmap
    initial_no_cells initial_no_objects initial_no_packets.
Proof.
  intros ge Gamma Hresolved id ty Hget.
  destruct (Hresolved _ _ Hget) as [b [fn [Hsymbol [Hfind Hty]]]]. subst ty.
  apply packet_variable_callable. eapply callable_variable_code; [apply PTree.gempty|exact Hsymbol|].
  split; [reflexivity|]. unfold type_of_function.
  repeat eexists; eauto.
Qed.

Lemma initial_code_heap : forall ge Gamma m,
  resolved_internal_globals ge Gamma ->
  initialized_heap_state ge Gamma empty_stcontext empty_vmap m
    initial_no_objects initial_no_cells initial_no_packets.
Proof.
  intros ge Gamma m Hresolved. constructor.
  - intros b ty Hget; rewrite PTree.gempty in Hget; discriminate.
  - constructor.
    + constructor; intros b ofs ty H; contradiction.
    + intros b ofs ty H; contradiction.
    + intros b ofs ty chunk H; contradiction.
    + intros b ofs ty chunk H; contradiction.
    + intros b ofs ty H; contradiction.
  - apply initial_code_bindings; assumption.
  - constructor; unfold packet_state_valid, packet_state_typed,
      packet_object_coverage, packet_layout_separated, packet_object_coherence;
      intros; contradiction.
  - exists (PTree.empty Z). split.
    + intros b limit Hget; rewrite PTree.gempty in Hget; discriminate.
    + intros b [[ty [Hget Hcode]]|[[ofs [ty [chunk Hfalse]]]|[[ofs [ty Hfalse]]|[ofs Hfalse]]]];
      try contradiction. rewrite PTree.gempty in Hget; discriminate.
Qed.

Theorem initial_code_configuration : forall p Gamma m e ef ty,
  type_program p -> Gamma = source_globals p ->
  resolved_internal_globals (globalenv p) Gamma ->
  (forall b fn, Genv.find_funct (globalenv p) (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) fn.(fn_body) /\
    frame_free fn.(fn_body)) ->
  type_expr p.(prog_comp_env) Gamma empty_stcontext e ef ty ->
  runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) e ->
  frame_free e ->
  program_runtime_configuration p Gamma Gamma empty_stcontext empty_vmap m
    initial_no_objects initial_no_cells initial_no_packets e ef ty.
Proof.
  intros p Gamma m e ef ty Hprogram Hgamma Hresolved Hbodies Htyped Hlocations Hframes.
  constructor.
  - constructor.
    + subst Gamma. apply typed_program_internal_code; assumption.
    + apply initial_code_bindings; assumption.
    + intros; eapply (proj1 (Hbodies _ _ H)); eauto.
    + intros; eapply (proj2 (Hbodies _ _ H)); eauto.
  - split.
    + constructor; auto using initial_code_heap, frame_free_initialized_frames.
    + apply empty_layout_coherent.
Qed.

Theorem code_only_loader_exists : forall p,
  (forall id gv, ~ In (id, Gvar gv) (AST.prog_defs (trans_program_astprog p))) ->
  exists m, Genv.init_mem (trans_program_astprog p) = Some m.
Proof. intros p Hnone. apply Genv.init_mem_exists. intros id gv Hin.
  exfalso; exact (Hnone id gv Hin). Qed.

Print Assumptions typed_program_internal_code.
Print Assumptions initial_code_configuration.
Print Assumptions code_only_loader_exists.

Corollary code_only_loaded_configuration : forall p e ef ty,
  type_program p ->
  (forall id gv, ~ In (id, Gvar gv) (AST.prog_defs (trans_program_astprog p))) ->
  resolved_internal_globals (globalenv p) (source_globals p) ->
  (forall b fn, Genv.find_funct (globalenv p) (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) fn.(fn_body) /\
    frame_free fn.(fn_body)) ->
  type_expr p.(prog_comp_env) (source_globals p) empty_stcontext e ef ty ->
  runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) e ->
  frame_free e ->
  exists m, Genv.init_mem (trans_program_astprog p) = Some m /\
    program_runtime_configuration p (source_globals p) (source_globals p)
      empty_stcontext empty_vmap m initial_no_objects initial_no_cells initial_no_packets e ef ty.
Proof.
  intros p e ef ty Htyped Hnodata Hglobals Hbodies He Hlocations Hframes.
  destruct (code_only_loader_exists p Hnodata) as [m Hload]. exists m; split; [exact Hload|].
  eapply initial_code_configuration; eauto.
Qed.
Print Assumptions code_only_loaded_configuration.

Definition global_definition_type (gd : AST.globdef fundef type) : type :=
  match gd with Gfun fn => type_of_fundef fn | Gvar gv => gv.(gvar_info) end.

Lemma bind_globals_definition_lookup : forall defs Gamma definitions,
  (forall id, Gamma ! id = option_map global_definition_type (definitions ! id)) ->
  forall id, (bind_globdef Gamma defs) ! id =
    option_map global_definition_type
      ((fold_left (fun tree def => PTree.set (fst def) (snd def) tree) defs definitions) ! id).
Proof.
  induction defs as [|[name def] defs IH]; intros Gamma definitions Hlookup id; simpl; auto.
  destruct def; apply IH; intros key; rewrite ! PTree.gsspec;
    destruct (peq key name); simpl; auto.
Qed.

Lemma source_globals_definition_lookup : forall p id,
  (source_globals p) ! id = option_map global_definition_type
    ((AST.prog_defmap (trans_program_astprog p)) ! id).
Proof.
  intros. apply bind_globals_definition_lookup. intros; rewrite !PTree.gempty; reflexivity.
Qed.

Theorem internal_definitions_resolve_globals : forall p,
  (forall id gd, In (id,gd) (AST.prog_defs (trans_program_astprog p)) ->
    exists fn, gd = Gfun (Internal fn)) ->
  resolved_internal_globals (globalenv p) (source_globals p).
Proof.
  intros p Hinternal id ty Hget. rewrite source_globals_definition_lookup in Hget.
  destruct ((AST.prog_defmap (trans_program_astprog p)) ! id) as [gd|] eqn:Hdef;
    simpl in Hget; try discriminate. inversion Hget; subst ty.
  destruct (proj1 (Genv.find_def_symbol (trans_program_astprog p) id gd) Hdef)
    as [b [Hsymbol Hlookup]].
  destruct (Genv.find_def_inversion _ _ Hlookup) as [name Hin].
  destruct (Hinternal name gd Hin) as [fn Hgd]. subst gd.
  exists b,fn. split; [exact Hsymbol|]. split; [|reflexivity].
  rewrite Genv.find_funct_find_funct_ptr. apply Genv.find_funct_ptr_iff. exact Hlookup.
Qed.
Print Assumptions internal_definitions_resolve_globals.

Theorem internal_source_loaded_configuration : forall p e ef ty,
  type_program p ->
  (forall id gd, In (id,gd) (AST.prog_defs (trans_program_astprog p)) ->
    exists fn, gd = Gfun (Internal fn)) ->
  (forall b fn, Genv.find_funct (globalenv p) (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
    runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) fn.(fn_body) /\
    frame_free fn.(fn_body)) ->
  type_expr p.(prog_comp_env) (source_globals p) empty_stcontext e ef ty ->
  runtime_locations (packet_heap_locations (globalenv p) initial_no_cells initial_no_objects initial_no_packets) e ->
  frame_free e ->
  exists m, Genv.init_mem (trans_program_astprog p) = Some m /\
    program_runtime_configuration p (source_globals p) (source_globals p)
      empty_stcontext empty_vmap m initial_no_objects initial_no_cells initial_no_packets e ef ty.
Proof.
  intros p e ef ty Hp Hinternal Hb He Hl Hf.
  apply code_only_loaded_configuration; auto using internal_definitions_resolve_globals.
  intros id gv Hin. destruct (Hinternal id (Gvar gv) Hin) as [fn Hbad]. discriminate.
Qed.
Print Assumptions internal_source_loaded_configuration.
