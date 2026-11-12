(* A reference parameter preserves an actual interior pointer. The pointed-to
   integer is allocated and initialized before the parameter slot is created. *)
Require Import List ZArith Lia AST Integers Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_soundness_arrays BeePL_callable_locations BeePL_scalar_parameters.

Definition regression_integer : type := Vtype (Tint I32 Signed noattr).
Definition regression_reference : type := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr).
Definition interior_integer_layout (target : Values.block) : scalar_layout :=
  fun b ofs ty chunk => b = target /\ ofs = Ptrofs.repr 4 /\
    ty = regression_integer /\ chunk = BMint32.

Lemma interior_offset_unsigned : Ptrofs.unsigned (Ptrofs.repr 4) = 4%Z.
Proof. apply Ptrofs.unsigned_repr. vm_compute. split; congruence. Qed.

Lemma interior_offset_nonzero : Ptrofs.repr 4 <> Ptrofs.zero.
Proof.
  intro Heq. apply (f_equal Ptrofs.unsigned) in Heq.
  rewrite interior_offset_unsigned, Ptrofs.unsigned_zero in Heq. discriminate.
Qed.

Theorem interior_reference_parameter_roundtrip : forall bge p name,
  exists initial target_ready parameter_ready final target slot Sigma,
    Mem.alloc Mem.empty 0 8 = (initial, target) /\
    Mem.store Mint32 initial target 4 (Values.Vint (Int.repr 17)) = Some target_ready /\
    Mem.alloc target_ready 0 (sizeof_type bge.(genv_cenv) regression_reference) =
      (parameter_ready, slot) /\
    Mem.store (transl_bchunk_cchunk (scalar_parameter_chunk regression_reference))
      parameter_ready slot 0 (Values.Vptr target (Ptrofs.repr 4)) = Some final /\
    bind_variables bge (PTree.set name (slot, regression_reference) empty_vmap)
      parameter_ready ((name, regression_reference) :: nil)
      (Vloc target (Ptrofs.repr 4) :: nil) final /\
    typed_memory_layout bge.(genv_cenv) Sigma (interior_integer_layout target) final /\
    type_expr bge.(genv_cenv) empty_context Sigma
      (Val (Vloc target (Ptrofs.repr 4)) regression_reference) nil regression_reference /\
    runtime_locations (callable_heap_locations bge (interior_integer_layout target))
      (Val (Vloc target (Ptrofs.repr 4)) regression_reference) /\
    deref_addr regression_reference final slot Ptrofs.zero Full (Vloc target (Ptrofs.repr 4)) /\
    ssem_expr bge p (PTree.set name (slot, regression_reference) empty_vmap) final
      (Var name regression_reference) final
      (PTree.set name (slot, regression_reference) empty_vmap)
      (Val (Vloc target (Ptrofs.repr 4)) regression_reference).
Proof.
  intros bge p name.
  destruct (Mem.alloc Mem.empty 0 8) as [initial target] eqn:Htargetalloc.
  set (Sigma := PTree.set target regression_reference empty_stcontext).
  assert (Hintscalar : scalar_parameter_type regression_integer).
  { split; [left; eexists; reflexivity|reflexivity]. }
  assert (Hinttyped : type_expr bge.(genv_cenv) empty_context Sigma
    (Val (Vint (Int.repr 17)) regression_integer) nil regression_integer) by constructor.
  assert (Hintfree : Mem.valid_access initial Mint32 target
    (Ptrofs.unsigned (Ptrofs.repr 4)) Freeable).
  { rewrite interior_offset_unsigned.
    eapply Mem.valid_access_alloc_same; [exact Htargetalloc|lia|simpl; lia|].
    exists 1%Z. reflexivity. }
  destruct (initialize_scalar_parameter bge bge.(genv_cenv) empty_context Sigma
    (fun _ _ _ => True) initial target (Ptrofs.repr 4) regression_integer (Vint (Int.repr 17))
    Hintscalar Hinttyped I Hintfree)
    as [target_ready [Hintstore [Hintassign [Hintcell Hintlocated]]]].
  change (Mem.store Mint32 initial target (Ptrofs.unsigned (Ptrofs.repr 4))
    (Values.Vint (Int.repr 17)) = Some target_ready) in Hintstore.
  rewrite interior_offset_unsigned in Hintstore.
  assert (Hreference : scalar_parameter_type regression_reference).
  { split; [right; left; do 2 eexists; reflexivity|reflexivity]. }
  assert (Htyped : type_expr bge.(genv_cenv) empty_context Sigma
    (Val (Vloc target (Ptrofs.repr 4)) regression_reference) nil regression_reference).
  { apply ty_valloc. unfold Sigma. apply PTree.gss. }
  assert (Hlocated : value_locations (callable_heap_locations bge (interior_integer_layout target))
    (Vloc target (Ptrofs.repr 4)) regression_reference).
  { simpl. left. exists (Reftype (Bprim (Tint I32 Signed noattr)) noattr), BMint32.
    split; [reflexivity|]. repeat split; reflexivity. }
  destruct (Mem.alloc target_ready 0 (sizeof_type bge.(genv_cenv) regression_reference))
    as [parameter_ready slot] eqn:Hslotalloc.
  assert (Hslotfree : Mem.valid_access parameter_ready
    (transl_bchunk_cchunk (scalar_parameter_chunk regression_reference)) slot
    (Ptrofs.unsigned Ptrofs.zero) Freeable).
  { rewrite Ptrofs.unsigned_zero.
    eapply Mem.valid_access_alloc_same; [exact Hslotalloc|lia| |].
    - rewrite (scalar_parameter_chunk_size bge.(genv_cenv) _ Hreference). lia.
    - exists 0%Z. lia. }
  destruct (initialize_scalar_parameter bge bge.(genv_cenv) empty_context Sigma
    (callable_heap_locations bge (interior_integer_layout target)) parameter_ready slot
    Ptrofs.zero regression_reference (Vloc target (Ptrofs.repr 4))
    Hreference Htyped Hlocated Hslotfree)
    as [final [Hptrstore [Hptrassign [Hptrcell Hptrlocated]]]].
  rewrite Ptrofs.unsigned_zero in Hptrstore.
  assert (Hread : deref_addr regression_reference final slot Ptrofs.zero Full
    (Vloc target (Ptrofs.repr 4))).
  { eapply deref_addr_value with
      (chunk := scalar_parameter_chunk regression_reference)
      (v := Values.Val.load_result
        (transl_bchunk_cchunk (scalar_parameter_chunk regression_reference))
        (Values.Vptr target (Ptrofs.repr 4))).
    - apply scalar_parameter_chunk_access; exact Hreference.
    - reflexivity.
    - simpl. eapply Mem.load_store_same; exact Hptrstore.
    - apply ordinary_reference_store_normalization. }
  exists initial, target_ready, parameter_ready, final, target, slot, Sigma.
  split; [reflexivity|]. split; [exact Hintstore|]. split; [exact Hslotalloc|].
  split; [exact Hptrstore|]. split.
  - econstructor; [apply PTree.gss|exact Hptrassign|constructor].
  - split.
    + intros b ofs ty chunk [Hb [Hofs [Hty Hchunk]]]. subst b ofs ty chunk.
      eapply typed_memory_cell_alloc_store_frame; eauto.
    + split; [exact Htyped|]. split; [exact Hlocated|]. split; [exact Hread|].
      eapply ssem_lvar; [apply PTree.gss|exact Hread].
Qed.

Print Assumptions interior_reference_parameter_roundtrip.
