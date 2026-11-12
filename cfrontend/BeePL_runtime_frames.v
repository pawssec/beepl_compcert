(* Captured call environments are part of runtime validity.  Literal address
   validity alone cannot justify a frame whose body reads a missing variable. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_callable_variables.
Require Import BeePL_callable_state.
Import ListNotations.

Record callable_heap_evolution (bge : genv) (Sigma : store_context)
    (layout : scalar_layout) (Sigma' : store_context) (m' : Mem.mem)
    (layout' : scalar_layout) : Prop := {
  heap_evolution_store : store_context_extends Sigma Sigma';
  heap_evolution_layout : forall b ofs ty chunk,
    layout b ofs ty chunk -> layout' b ofs ty chunk;
  heap_evolution_blocks : store_blocks_valid Sigma' m';
  heap_evolution_memory : typed_memory_layout bge.(genv_cenv) Sigma' layout' m';
  heap_evolution_contents : memory_locations (callable_heap_locations bge layout') layout' m'
}.

Lemma callable_state_evolve : forall bge Gamma Sigma vm m layout Sigma' m' layout',
  callable_heap_state Gamma Sigma bge vm m layout ->
  callable_heap_evolution bge Sigma layout Sigma' m' layout' ->
  callable_heap_state Gamma Sigma' bge vm m' layout'.
Proof.
  intros bge Gamma Sigma vm m layout Sigma' m' layout' Hstate Hupdate.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  destruct Hupdate as [Hext Hinc Hblocks' Hmemory' Hcontents'].
  constructor; try assumption. eapply callable_variable_layout_extend; eauto.
Qed.

Lemma callable_heap_evolution_refl : forall bge Gamma Sigma vm m layout,
  callable_heap_state Gamma Sigma bge vm m layout ->
  callable_heap_evolution bge Sigma layout Sigma m layout.
Proof.
  intros bge Gamma Sigma vm m layout [Hblocks Hmemory Hcontents Hbindings].
  constructor; auto using store_context_extends_refl.
Qed.

Lemma callable_heap_evolution_trans : forall bge Sigma layout Sigma' m' layout' Sigma'' m'' layout'',
  callable_heap_evolution bge Sigma layout Sigma' m' layout' ->
  callable_heap_evolution bge Sigma' layout' Sigma'' m'' layout'' ->
  callable_heap_evolution bge Sigma layout Sigma'' m'' layout''.
Proof.
  intros bge Sigma layout Sigma' m' layout' Sigma'' m'' layout''
    [Hext Hinc Hblocks Hmemory Hcontents] [Hext' Hinc' Hblocks' Hmemory' Hcontents'].
  constructor; try assumption; eauto using store_context_extends_trans.
Qed.

Fixpoint runtime_frames (bge : genv) (Sigma : store_context) (m : Mem.mem)
    (layout : scalar_layout) (e : expr) : Prop :=
  match e with
  | CallFrame callee body ty => exists Gamma ef,
      callable_heap_state Gamma Sigma bge callee m layout /\
      type_expr bge.(genv_cenv) Gamma Sigma body ef ty /\
      runtime_frames bge Sigma m layout body
  | LoopFrame _ template active => runtime_frames bge Sigma m layout template /\
      runtime_frames bge Sigma m layout active
  | App f es _ => runtime_frames bge Sigma m layout f /\
      all_expr_locations (runtime_frames bge Sigma m layout) es
  | Prim _ es _ | Sinit _ _ es _ | Ebytes es _ | Ainit _ _ es _ =>
      all_expr_locations (runtime_frames bge Sigma m layout) es
  | Bind _ _ first body _ => runtime_frames bge Sigma m layout first /\
      runtime_frames bge Sigma m layout body
  | Cond guard yes no _ | For guard yes _ no _ =>
      runtime_frames bge Sigma m layout guard /\
      runtime_frames bge Sigma m layout yes /\ runtime_frames bge Sigma m layout no
  | Sfield body _ _ | Esome body _ => runtime_frames bge Sigma m layout body
  | Match scrutinee _ branches _ => runtime_frames bge Sigma m layout scrutinee /\
      all_expr_locations (runtime_frames bge Sigma m layout) branches
  | _ => True
  end.

Record runtime_configuration (bge : genv) (Gamma : ty_context) (Sigma : store_context)
    (vm : vmap) (m : Mem.mem) (layout : scalar_layout) (e : expr) (ef : effect)
    (ty : type) : Prop := {
  runtime_config_heap : callable_heap_state Gamma Sigma bge vm m layout;
  runtime_config_typing : type_expr bge.(genv_cenv) Gamma Sigma e ef ty;
  runtime_config_locations : runtime_locations (callable_heap_locations bge layout) e;
  runtime_config_frames : runtime_frames bge Sigma m layout e
}.

Lemma runtime_frames_evolve : forall bge Sigma m layout Sigma' m' layout',
  callable_heap_evolution bge Sigma layout Sigma' m' layout' ->
  forall e, runtime_frames bge Sigma m layout e -> runtime_frames bge Sigma' m' layout' e.
Proof.
  intros bge Sigma m layout Sigma' m' layout' Hupdate e.
  induction e using expr_ind_rec; intros Hframes; simpl in *;
    try solve [intuition eauto];
    try solve [rewrite all_expr_locations_Forall, Forall_forall in *; eauto].
  all: try solve [repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto; rewrite all_expr_locations_Forall; apply Forall_forall;
    intros child Hin;
    match goal with IH : forall e, In e ?es -> _, Hall : all_expr_locations _ ?es |- _ =>
      apply IH; [exact Hin | rewrite all_expr_locations_Forall, Forall_forall in Hall; apply Hall; exact Hin]
    end].
  destruct Hframes as [Gamma [ef [Hstate [Htyped Hnested]]]].
  exists Gamma, ef. split.
  - eapply callable_state_evolve; eauto.
  - split; [|auto]. eapply (proj2 typing_store_extension); [exact Htyped |].
    exact (heap_evolution_store _ _ _ _ _ _ Hupdate).
Qed.

Lemma runtime_configuration_evolve : forall bge Gamma Sigma vm m layout e ef ty Sigma' m' layout',
  runtime_configuration bge Gamma Sigma vm m layout e ef ty ->
  callable_heap_evolution bge Sigma layout Sigma' m' layout' ->
  runtime_configuration bge Gamma Sigma' vm m' layout' e ef ty.
Proof.
  intros bge Gamma Sigma vm m layout e ef ty Sigma' m' layout'
    [Hstate Htyped Hlocations Hframes] Hupdate. constructor.
  - eapply callable_state_evolve; eauto.
  - eapply (proj2 typing_store_extension); [exact Htyped |].
    exact (heap_evolution_store _ _ _ _ _ _ Hupdate).
  - eapply runtime_locations_monotone; [|exact Hlocations].
    apply callable_heap_locations_monotone.
    exact (heap_evolution_layout _ _ _ _ _ _ Hupdate).
  - eapply runtime_frames_evolve; eauto.
Qed.

Print Assumptions callable_state_evolve.
Print Assumptions runtime_frames_evolve.
Print Assumptions runtime_configuration_evolve.
