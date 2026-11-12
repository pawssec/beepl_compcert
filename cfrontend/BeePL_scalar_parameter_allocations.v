(* Parameter slot permissions derive from actual allocations. These facts do
   not claim that newly allocated memory is already initialized. *)
Require Import List ZArith Lia AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_allocation_proofs BeePL_call_bindings.
Require Import BeePL_parameter_allocations.
Import ListNotations.
Local Open Scope Z_scope.

Lemma allocated_parameter_chunk_access :
  forall bge Sigma vm m params callee allocated Sigma',
  alloc_variables bge Sigma vm m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  forall id ty, In (id, ty) params -> exists b,
    PTree.get id callee = Some (b, ty) /\
    forall chunk, size_chunk chunk <= sizeof_type (genv_cenv bge) ty ->
      Mem.valid_access allocated chunk b 0 Freeable.
Proof.
  intros bge Sigma vm m params callee allocated Sigma' Halloc.
  induction Halloc as [Sigma vm m|Sigma vm m id ty params first fresh final result Sigma1 Sigma'
    Hballoc Htail IH]; intros Hnames name t Hin.
  - contradiction.
  - inversion Hnames as [|? ? Hnotin Htailnames]; subst.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst name t.
      unfold balloc in Hballoc.
      destruct (Mem.alloc m 0 (sizeof_type (genv_cenv bge) ty)) as [mem block] eqn:Hmem.
      inversion Hballoc; subst mem block Sigma1.
      exists fresh. split.
      * rewrite (alloc_variables_unshadowed_lookup _ _ _ _ _ _ _ _ Htail id Hnotin).
        apply PTree.gss.
      * intros chunk Hsize.
        eapply parameter_allocations_access_frame; [exact Htail |].
        eapply Mem.valid_access_alloc_same; [exact Hmem | lia | lia |].
        exists 0. lia.
    + eapply IH; eauto.
Qed.

Print Assumptions allocated_parameter_chunk_access.

Require Import BeePL_scalar_parameters.

Theorem scalar_parameter_allocation_slots :
  forall bge Sigma vm m params callee allocated Sigma',
  alloc_variables bge Sigma vm m params callee allocated Sigma' ->
  NoDup (map fst params) ->
  Forall (fun param => scalar_parameter_type (snd param)) params ->
  (forall id ty, In (id, ty) params -> exists b,
    PTree.get id callee = Some (b, ty) /\ ~ Mem.valid_block m b /\
    Mem.valid_block allocated b /\
    Mem.valid_access allocated (transl_bchunk_cchunk (scalar_parameter_chunk ty))
      b 0 Freeable) /\
  parameter_targets_distinct callee params.
Proof.
  intros bge Sigma vm m params callee allocated Sigma' Halloc Hnames Htypes.
  destruct (parameter_allocation_slots _ _ _ _ _ _ _ _ Halloc Hnames)
    as [Hslots Hdistinct]. split; [|exact Hdistinct].
  intros id ty Hin.
  destruct (Hslots id ty Hin) as [b [Hget [Hfresh [Hvalid Hprimitive]]]].
  destruct (allocated_parameter_chunk_access _ _ _ _ _ _ _ _ Halloc Hnames id ty Hin)
    as [target [Htarget Haccess]].
  assert (target = b) by congruence. subst target.
  exists b. split; [exact Hget |]. split; [exact Hfresh |].
  split; [exact Hvalid |]. apply Haccess.
  rewrite (scalar_parameter_chunk_size (genv_cenv bge) ty); [lia |].
  rewrite Forall_forall in Htypes. exact (Htypes _ Hin).
Qed.

Theorem scalar_parameters_allocate : forall bge Sigma m params,
  NoDup (map fst params) ->
  Forall (fun param => scalar_parameter_type (snd param)) params ->
  exists callee allocated Sigma',
    alloc_variables bge Sigma empty_vmap m params callee allocated Sigma' /\
    (forall id ty, In (id, ty) params -> exists b,
      PTree.get id callee = Some (b, ty) /\ ~ Mem.valid_block m b /\
      Mem.valid_block allocated b /\
      Mem.valid_access allocated (transl_bchunk_cchunk (scalar_parameter_chunk ty))
        b 0 Freeable) /\
    parameter_targets_distinct callee params.
Proof.
  intros bge Sigma m params Hnames Htypes.
  destruct (alloc_variables_total bge params Sigma empty_vmap m)
    as [callee [allocated [Sigma' Halloc]]].
  exists callee, allocated, Sigma'. split; [exact Halloc |].
  eapply scalar_parameter_allocation_slots; eauto.
Qed.

Print Assumptions scalar_parameter_allocation_slots.
Print Assumptions scalar_parameters_allocate.
