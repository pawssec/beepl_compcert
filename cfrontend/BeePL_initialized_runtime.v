(* Runtime configurations share one initialized-object heap across all captured
   call environments. Each captured map has its own static binding context. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_callable_variables BeePL_aggregate_memory.
Require Import BeePL_object_coverage BeePL_context_retyping BeePL_frame_free.
Require Import BeePL_heap_extents.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Record initialized_heap_state (ge : genv) (Gamma : ty_context) (Sigma : store_context)
    (vm : vmap) (m : Mem.mem) (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations) : Prop := {
  initialized_heap_blocks : store_blocks_valid Sigma m;
  initialized_heap_memory : initialized_object_memory ge Sigma m objects cells;
  initialized_heap_bindings : packet_variable_layout Gamma Sigma ge vm cells objects packets;
  initialized_heap_packets : packet_heap_invariant ge Sigma m objects cells packets;
  initialized_heap_extents : heap_block_extents Sigma m objects cells packets
}.

Record initialized_heap_evolution (ge : genv) (Sigma : store_context)
    (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations)
    (Sigma' : store_context) (m' : Mem.mem)
    (objects' : aggregate_object_context) (cells' : scalar_layout) (packets' : packet_locations) : Prop := {
  initialized_evolution_store : store_context_extends Sigma Sigma';
  initialized_evolution_cells : forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk;
  initialized_evolution_objects : forall b ofs ty, objects b ofs ty -> objects' b ofs ty;
  initialized_evolution_blocks : store_blocks_valid Sigma' m';
  initialized_evolution_memory : initialized_object_memory ge Sigma' m' objects' cells';
  initialized_evolution_packet_locations : forall b ofs, packets b ofs -> packets' b ofs;
  initialized_evolution_packets : packet_heap_invariant ge Sigma' m' objects' cells' packets';
  initialized_evolution_extents : heap_block_extents Sigma' m' objects' cells' packets'
}.

Lemma initialized_heap_state_evolve :
  forall ge Gamma Sigma vm m objects cells packets Sigma' m' objects' cells' packets',
  initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_heap_state ge Gamma Sigma' vm m' objects' cells' packets'.
Proof.
  intros ge Gamma Sigma vm m objects cells packets Sigma' m' objects' cells' packets'
    [Hblocks Hmemory Hbindings Hpacketstate Hextents] [Hext Hcells Hobjects Hblocks' Hmemory' Hpackets Hpacketstate' Hextents'].
  constructor; try assumption. eapply packet_variable_layout_extend; eauto.
Qed.

Lemma initialized_heap_evolution_refl : forall ge Gamma Sigma vm m objects cells packets,
  initialized_heap_state ge Gamma Sigma vm m objects cells packets ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets.
Proof. intros ge Gamma Sigma vm m objects cells packets [Hblocks Hmemory Hbindings Hpacketstate Hextents].
  constructor; auto using store_context_extends_refl. Qed.

Lemma initialized_heap_evolution_trans :
  forall ge Sigma objects cells packets Sigma' m' objects' cells' packets' Sigma'' m'' objects'' cells'' packets'',
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_heap_evolution ge Sigma' objects' cells' packets' Sigma'' m'' objects'' cells'' packets'' ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma'' m'' objects'' cells'' packets''.
Proof.
  intros ge Sigma objects cells packets Sigma' m' objects' cells' packets' Sigma'' m'' objects'' cells'' packets''
    [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents] [Hext' Hcells' Hobjects' Hblocks' Hmemory' Hpackets' Hpacketstate' Hextents'].
  constructor; eauto using store_context_extends_trans.
Qed.

Fixpoint initialized_runtime_frames (ge : genv) (Sigma : store_context)
    (cells : scalar_layout) (objects : aggregate_object_context) (packets : packet_locations) (e : expr) : Prop :=
  match e with
  | CallFrame callee body ty => exists Gamma ef,
      packet_variable_layout Gamma Sigma ge callee cells objects packets /\
      type_expr ge.(genv_cenv) Gamma Sigma body ef ty /\
      initialized_runtime_frames ge Sigma cells objects packets body
  | LoopFrame _ template active => initialized_runtime_frames ge Sigma cells objects packets template /\
      initialized_runtime_frames ge Sigma cells objects packets active
  | App f es _ => initialized_runtime_frames ge Sigma cells objects packets f /\
      all_expr_locations (initialized_runtime_frames ge Sigma cells objects packets) es
  | Prim _ es _ | Sinit _ _ es _ | Ebytes es _ | Ainit _ _ es _ =>
      all_expr_locations (initialized_runtime_frames ge Sigma cells objects packets) es
  | Bind _ _ first body _ => initialized_runtime_frames ge Sigma cells objects packets first /\
      initialized_runtime_frames ge Sigma cells objects packets body
  | Cond guard yes no _ | For guard yes _ no _ =>
      initialized_runtime_frames ge Sigma cells objects packets guard /\
      initialized_runtime_frames ge Sigma cells objects packets yes /\ initialized_runtime_frames ge Sigma cells objects packets no
  | Sfield body _ _ | Esome body _ => initialized_runtime_frames ge Sigma cells objects packets body
  | Match scrutinee _ branches _ => initialized_runtime_frames ge Sigma cells objects packets scrutinee /\
      all_expr_locations (initialized_runtime_frames ge Sigma cells objects packets) branches
  | _ => True
  end.

Record initialized_runtime_configuration (ge : genv) (Gamma : ty_context) (Sigma : store_context)
    (vm : vmap) (m : Mem.mem) (objects : aggregate_object_context) (cells : scalar_layout) (packets : packet_locations)
    (e : expr) (ef : effect) (ty : type) : Prop := {
  initialized_config_heap : initialized_heap_state ge Gamma Sigma vm m objects cells packets;
  initialized_config_typing : type_expr ge.(genv_cenv) Gamma Sigma e ef ty;
  initialized_config_locations : runtime_locations (packet_heap_locations ge cells objects packets) e;
  initialized_config_frames : initialized_runtime_frames ge Sigma cells objects packets e
}.

Lemma initialized_runtime_frames_evolve : forall ge Sigma cells objects packets Sigma' cells' objects' packets',
  store_context_extends Sigma Sigma' ->
  (forall b ofs ty chunk, cells b ofs ty chunk -> cells' b ofs ty chunk) ->
  (forall b ofs ty, objects b ofs ty -> objects' b ofs ty) ->
  (forall b ofs, packets b ofs -> packets' b ofs) ->
  forall e, initialized_runtime_frames ge Sigma cells objects packets e -> initialized_runtime_frames ge Sigma' cells' objects' packets' e.
Proof.
  intros ge Sigma cells objects packets Sigma' cells' objects' packets' Hext Hinc Hobjects Hpackets e.
  induction e using expr_ind_rec; intros Hframes; simpl in *;
    try solve [intuition eauto];
    try solve [rewrite all_expr_locations_Forall, Forall_forall in *; eauto].
  all: try solve [repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto; rewrite all_expr_locations_Forall; apply Forall_forall;
    intros child Hin;
    match goal with IH : forall e, In e ?es -> _, Hall : all_expr_locations _ ?es |- _ =>
      apply IH; [exact Hin | rewrite all_expr_locations_Forall, Forall_forall in Hall; apply Hall; exact Hin]
    end].
  destruct Hframes as [Gamma [ef [Hbindings [Htyped Hnested]]]].
  exists Gamma, ef. split.
  - eapply packet_variable_layout_extend; eauto.
  - split; [|auto]. eapply (proj2 typing_store_extension); eauto.
Qed.

Lemma initialized_runtime_configuration_evolve :
  forall ge Gamma Sigma vm m objects cells packets e ef ty Sigma' m' objects' cells' packets',
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  initialized_runtime_configuration ge Gamma Sigma' vm m' objects' cells' packets' e ef ty.
Proof.
  intros ge Gamma Sigma vm m objects cells packets e ef ty Sigma' m' objects' cells' packets'
    [Hstate Htyped Hlocations Hframes] Hupdate.
  destruct Hupdate as [Hext Hcells Hobjects Hblocks Hmemory Hpackets Hpacketstate Hextents]. constructor.
  - eapply initialized_heap_state_evolve; [exact Hstate | constructor; eassumption].
  - eapply (proj2 typing_store_extension); eauto.
  - eapply runtime_locations_monotone; [|exact Hlocations].
    apply packet_heap_locations_monotone; assumption.
  - eapply initialized_runtime_frames_evolve; eauto.
Qed.

Lemma frame_free_initialized_frames : forall ge Sigma cells objects packets e,
  frame_free e -> initialized_runtime_frames ge Sigma cells objects packets e.
Proof.
  intros ge Sigma cells objects packets e. induction e using expr_ind_rec; simpl; intros Hfree;
    try solve [contradiction | exact I | intuition eauto].
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try split; auto;
    rewrite all_expr_locations_Forall in *; apply Forall_forall; intros child Hin;
    match goal with IH : forall e, In e ?es -> _, Hall : Forall _ ?es |- _ =>
      apply IH; [exact Hin | rewrite Forall_forall in Hall; apply Hall; exact Hin]
    end.
Qed.

Theorem initialized_frame_return :
  forall ge p Gamma Sigma caller callee m objects cells packets v ty ef,
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (CallFrame callee (Val v ty) ty) ef ty ->
  ssem_expr ge p caller m (CallFrame callee (Val v ty) ty) m caller (Val v ty) /\
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets (Val v ty) ef ty.
Proof.
  intros ge p Gamma Sigma caller callee m objects cells packets v ty ef
    [Hheap Htyping Hlocations Hframes].
  split; [apply ssem_call_frame_return |]. constructor.
  - exact Hheap.
  - inversion Htyping; subst. eapply value_typing_context_independent; eauto.
  - exact Hlocations.
  - exact I.
Qed.

Theorem initialized_frame_configuration_body :
  forall ge Gamma Sigma caller callee m objects cells packets body ef ty,
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (CallFrame callee body ty) ef ty ->
  exists callee_Gamma,
    initialized_runtime_configuration ge callee_Gamma Sigma callee m objects cells packets body ef ty.
Proof.
  intros ge Gamma Sigma caller callee m objects cells packets body ef ty
    [[Hblocks Hmemory Hcaller Hpacketstate Hextents] Htyping Hlocations Hframes].
  simpl in Hframes. destruct Hframes as [callee_Gamma [bodyef [Hcallee [Hbody Hnested]]]].
  exists callee_Gamma. constructor.
  - constructor; assumption.
  - inversion Htyping; subst. eapply expression_context_retyping; [eassumption | exact Hbody].
  - exact Hlocations.
  - exact Hnested.
Qed.

(* The body configuration is the induction hypothesis for the actual body
   step; this lemma does not assert that every expression preserves it. *)
Theorem initialized_frame_body_step :
  forall ge p Gamma callee_Gamma Sigma caller callee m objects cells packets body ef ty
    Sigma' callee' m' objects' cells' packets' body' ef',
  initialized_runtime_configuration ge Gamma Sigma caller m objects cells packets
    (CallFrame callee body ty) ef ty ->
  ssem_expr ge p callee m body m' callee' body' ->
  initialized_runtime_configuration ge callee_Gamma Sigma' callee' m' objects' cells' packets' body' ef' ty ->
  initialized_heap_evolution ge Sigma objects cells packets Sigma' m' objects' cells' packets' ->
  sub_effect ef' ef = true ->
  ssem_expr ge p caller m (CallFrame callee body ty) m' caller (CallFrame callee' body' ty) /\
  initialized_runtime_configuration ge Gamma Sigma' caller m' objects' cells' packets'
    (CallFrame callee' body' ty) ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros ge p Gamma callee_Gamma Sigma caller callee m objects cells packets body ef ty
    Sigma' callee' m' objects' cells' packets' body' ef'
    [Hcaller Htyped Hlocations Hframes] Hstep
    [Hcallee Hbody Hbodylocations Hbodyframes] Hupdate Heffect.
  split; [eapply ssem_call_frame_step; exact Hstep |]. split; [|exact Heffect]. constructor.
  - eapply initialized_heap_state_evolve; eauto.
  - eapply ty_callframe; exact Hbody.
  - exact Hbodylocations.
  - simpl. exists callee_Gamma, ef'. split.
    + exact (initialized_heap_bindings _ _ _ _ _ _ _ _ Hcallee).
    + split; assumption.
Qed.

Print Assumptions initialized_runtime_configuration_evolve.
Print Assumptions initialized_frame_return.
Print Assumptions initialized_frame_configuration_body.
Print Assumptions initialized_frame_body_step.
