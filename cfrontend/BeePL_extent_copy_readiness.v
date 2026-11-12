(* Whole-object copy readiness follows from typed provenance, source-owned
   allocation extents, and runtime locations. No next-state premise is used. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy BeePL_object_coverage.
Require Import BeePL_object_separation BeePL_block_extents BeePL_heap_extents.
Require Import BeePL_soundness_arrays BeePL_runtime_locations BeePL_packet_bindings.
Require Import BeePL_packet_location_coherence BeePL_callable_array_objects.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_initialized_aggregate_mutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tracked_aggregate_freeable : forall ge Sigma m objects cells packets b base ty,
  initialized_object_memory ge Sigma m objects cells ->
  heap_block_extents Sigma m objects cells packets -> objects b base ty ->
  Mem.range_perm m b (Ptrofs.unsigned base)
    (Ptrofs.unsigned base + sizeof_type ge.(genv_cenv) ty) Cur Freeable.
Proof.
  intros * Hmemory Hextents Hobject.
  destruct (heap_extent_lookup _ _ _ _ _ _ Hextents
    (or_intror (or_intror (or_introl (ex_intro _ base (ex_intro _ ty Hobject))))))
    as [limit Hextent].
  eapply source_extent_readable_freeable; [exact Hextent|].
  destruct (aggregate_object_readable _ _ _ _
    (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hobject)
    as [_ [_ [_ [_ Hread]]]]. exact Hread.
Qed.

Theorem program_tracked_aggregate_copy_ready :
  forall p Sigma m objects cells packets ty src source dst target,
  initialized_object_memory (globalenv p) Sigma m objects cells ->
  heap_block_extents Sigma m objects cells packets ->
  objects src source ty -> objects dst target ty ->
  aggregate_copy_ready (globalenv p) m ty src source dst target.
Proof.
  intros * Hmemory Hextents Hsource Htarget.
  eapply program_aggregate_copy_ready;
    [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hsource|exact Htarget|].
  exact (tracked_aggregate_freeable (globalenv p) Sigma m objects cells packets dst target ty
    Hmemory Hextents Htarget).
Qed.

Lemma located_basic_aggregate_readable :
  forall ge Sigma m objects cells packets b base basic,
  initialized_object_memory ge Sigma m objects cells ->
  heap_block_extents Sigma m objects cells packets ->
  is_aggregate_type (construct_type_btype basic) = true ->
  object_type_at ge.(genv_cenv) Sigma b (Ptrofs.unsigned base) (construct_type_btype basic) ->
  packet_heap_locations ge cells objects packets b base (construct_type_btype basic) ->
  aggregate_readable ge.(genv_cenv) m b base (construct_type_btype basic).
Proof.
  intros * Hmemory Hextents Hkind Htype Hlocation.
  destruct Hlocation as [Hlocation|[Hbytes Hpacket]]; [|destruct basic; discriminate Hbytes].
  destruct Hlocation as [Hcall|[[Haggregate Hobject]|[bt [attr [Heq Hobject]]]]].
  - destruct basic as [pt|sid attr|pt len attr]; simpl in *; [discriminate Hkind| |].
    + destruct Hcall as [[pt [chunk [Heq Hcell]]]|[elem [len [arrayAttr [Heq Hrest]]]]]; discriminate Heq.
    + destruct Hcall as [[pointer [chunk [Heq Hcell]]]|Harray]; [discriminate Heq|].
      exact (proj1 (callable_primitive_array_readable _ _ _ _ _ _ _ _ _ _ _
        Hmemory Hextents Htype Harray)).
  - eapply aggregate_object_readable; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hobject].
  - destruct basic; discriminate Heq.
Qed.

Theorem program_located_aggregate_copy_ready :
  forall p Gamma Sigma m objects cells packets basic attr src source dst target ef,
  initialized_object_memory (globalenv p) Sigma m objects cells ->
  heap_block_extents Sigma m objects cells packets ->
  is_aggregate_type (construct_type_btype basic) = true ->
  type_expr p.(prog_comp_env) Gamma Sigma
    (Val (Vloc src source) (construct_type_btype basic)) ef (construct_type_btype basic) ->
  packet_heap_locations (globalenv p) cells objects packets src source (construct_type_btype basic) ->
  packet_heap_locations (globalenv p) cells objects packets dst target (Ptrtype (Reftype basic attr)) ->
  aggregate_copy_ready (globalenv p) m (construct_type_btype basic) src source dst target.
Proof.
  intros * Hmemory Hextents Hkind Htyped Hsource Htarget.
  pose proof (aggregate_value_object_provenance _ _ _ _ _ _ _ Hkind Htyped) as Htype.
  pose proof (located_aggregate_reference_object _ _ _ _ _ _ _ _ _ _ Hmemory Hkind Htarget) as Hobject.
  pose proof (initialized_object_descriptors _ _ _ _ _ Hmemory) as Hobjects.
  destruct (located_basic_aggregate_readable _ _ _ _ _ _ _ _ _ Hmemory Hextents Hkind Htype Hsource)
    as [_ [Hsize [HsourceBound [HsourceValid Hread]]]].
  destruct (aggregate_object_readable _ _ _ _ Hobjects _ _ _ Hobject)
    as [_ [_ [HtargetBound [HtargetValid HtargetRead]]]].
  assert (Hwrite := tracked_aggregate_freeable _ _ _ _ _ _ _ _ _ Hmemory Hextents Hobject).
  constructor; try assumption.
  - eapply program_typed_object_copy_alignment; exact Htype.
  - eapply program_typed_object_copy_alignment. eapply aggregate_object_typing; eauto.
  - eapply program_aggregate_value_reference_nonoverlap; eauto.
Qed.

Lemma coherent_assignment_copy_ready :
  forall p Gamma Sigma vm m objects cells packets basic attr src source dst target ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) ef Utype ->
  is_aggregate_type (construct_type_btype basic) = true ->
  aggregate_copy_ready (globalenv p) m (construct_type_btype basic) src source dst target.
Proof.
  intros * [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes] Hcoherent] Hkind.
  destruct (type_infer_massgn _ _ _ _ _ _ _ _ Htyped)
    as [_ [_ [pt [ef1 [ef2 [Hleft [Hoption Hright]]]]]]].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as HleftType.
  simpl in HleftType. inversion HleftType; subst pt.
  eapply program_located_aggregate_copy_ready;
    [exact Hmemory|exact Hextents|exact Hkind|exact Hright|exact (proj1 (proj2 Hlocations))|exact (proj1 Hlocations)].
Qed.

Theorem program_coherent_aggregate_assignment_progress :
  forall p Gamma Sigma vm m objects cells packets basic attr src source dst target ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) ef Utype ->
  is_aggregate_type (construct_type_btype basic) = true ->
  exists final,
    ssem_expr (globalenv p) p vm m
      (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
        Val (Vloc src source) (construct_type_btype basic)] Utype) final vm (Val Vunit Utype) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm final objects cells packets (Val Vunit Utype) nil Utype.
Proof.
  intros * Hconfig Hkind. eapply coherent_aggregate_assignment_progress;
    [exact Hconfig|]. eapply coherent_assignment_copy_ready; eauto.
Qed.

Theorem program_coherent_aggregate_assignment_preservation :
  forall p Gamma Sigma vm m objects cells packets basic attr src source dst target ef final vm' e',
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) ef Utype ->
  is_aggregate_type (construct_type_btype basic) = true ->
  ssem_expr (globalenv p) p vm m
    (Prim Massgn [Val (Vloc dst target) (Ptrtype (Reftype basic attr));
      Val (Vloc src source) (construct_type_btype basic)] Utype) final vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm' final objects cells packets e' nil Utype /\
  sub_effect nil ef = true.
Proof.
  intros * Hconfig Hkind Hstep. eapply coherent_aggregate_assignment_preservation;
    [exact Hconfig| |exact Hstep]. eapply coherent_assignment_copy_ready; eauto.
Qed.

Print Assumptions program_coherent_aggregate_assignment_progress.
Print Assumptions program_coherent_aggregate_assignment_preservation.
