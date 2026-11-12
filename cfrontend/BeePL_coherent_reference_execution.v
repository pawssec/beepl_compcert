Require Import BeePL_heap_extents BeePL_block_extents.
(* Connected execution: allocate an int reference, overwrite it, read back 73.
   Both allocations and writes use the coherent configuration theorems. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_initialization_proofs BeePL_aggregate_memory BeePL_object_coverage.
Require Import BeePL_structure_proofs.
Require Import BeePL_initialized_runtime BeePL_layout_coherence BeePL_coherent_configurations.
Require Import BeePL_coherent_references.
Require Import BeePL_packet_object_layout.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_packet_state BeePL_packet_coverage.
Import ListNotations.
Local Open Scope Z_scope.

Definition execution_int : type := Vtype (Tint I32 Signed noattr).
Definition execution_reference : type := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr).
Definition execution_no_cells : scalar_layout := fun _ _ _ _ => False.
Definition execution_no_objects : aggregate_object_context := fun _ _ _ => False.
Definition execution_no_packets : packet_locations := fun _ _ => False.

Theorem coherent_reference_write_read_execution : forall ge p,
  exists first final fresh,
    ssem_expr ge p empty_vmap Mem.empty
      (Prim Ref [Val (Vint (Int.repr 41)) execution_int] execution_reference)
      first empty_vmap (Val (Vloc fresh Ptrofs.zero) execution_reference) /\
    ssem_expr ge p empty_vmap first
      (Prim Massgn [Val (Vloc fresh Ptrofs.zero) execution_reference;
                   Val (Vint (Int.repr 73)) execution_int] Utype)
      final empty_vmap (Val Vunit Utype) /\
    ssem_expr ge p empty_vmap final
      (Prim Deref [Val (Vloc fresh Ptrofs.zero) execution_reference] execution_int)
      final empty_vmap (Val (Vint (Int.repr 73)) execution_int) /\
    coherent_runtime_configuration ge empty_context
      (PTree.set fresh execution_reference empty_stcontext) empty_vmap final execution_no_objects
      (extend_scalar_layout execution_no_cells fresh Ptrofs.zero execution_int BMint32) execution_no_packets
      (Val (Vint (Int.repr 73)) execution_int) nil execution_int.
Proof.
  intros ge p.
  assert (Hstart : coherent_runtime_configuration ge empty_context empty_stcontext empty_vmap Mem.empty
    execution_no_objects execution_no_cells execution_no_packets
    (Prim Ref [Val (Vint (Int.repr 41)) execution_int] execution_reference) [Alloc] execution_reference).
  { split.
    - constructor.
      + constructor.
        * intros b ty Hget. rewrite PTree.gempty in Hget. discriminate.
        * constructor.
          -- constructor; intros b ofs ty H; contradiction.
          -- intros b ofs ty H; contradiction.
          -- intros b ofs ty chunk H; contradiction.
          -- intros b ofs ty chunk H; contradiction.
          -- intros b ofs ty H; contradiction.
        * intros id ty Hget. rewrite PTree.gempty in Hget. discriminate.
        * constructor; unfold packet_state_valid, packet_state_typed, packet_object_coverage, packet_layout_separated, packet_object_coherence; intros; contradiction.
        * exists (PTree.empty Z). split.
          -- intros b limit Hget. rewrite PTree.gempty in Hget. discriminate.
          -- intros b [[ty [Hget Hcode]]|[[ofs [ty [chunk Hfalse]]]|[[ofs [ty Hfalse]]|[ofs Hfalse]]]];
               try contradiction. rewrite PTree.gempty in Hget; discriminate.
      + change [Alloc] with ([] ++ [Alloc]). apply ty_ref; [apply ty_vali |reflexivity].
      + simpl. auto.
      + simpl. auto.
    - apply empty_layout_coherent. }
  destruct (coherent_primitive_reference_progress ge empty_context empty_stcontext empty_vmap Mem.empty
    execution_no_objects execution_no_cells execution_no_packets p (Tint I32 Signed noattr) noattr (Vint (Int.repr 41)) [Alloc]
    Hstart) as [first [fresh [Href [Hgrow [Hrefconfig Hcoherent]]]]].
  destruct Hrefconfig as [Hheap Hreftyped Hreflocated Hrefframes].
  assert (Hwriteconfig : coherent_runtime_configuration ge empty_context
    (PTree.set fresh execution_reference empty_stcontext) empty_vmap first execution_no_objects
    (extend_scalar_layout execution_no_cells fresh Ptrofs.zero execution_int BMint32) execution_no_packets
    (Prim Massgn [Val (Vloc fresh Ptrofs.zero) execution_reference;
                 Val (Vint (Int.repr 73)) execution_int] Utype) [Write] Utype).
  { split; [|exact Hcoherent]. constructor.
    - exact Hheap.
    - change [Write] with ([] ++ [] ++ [Write]).
      eapply ty_massgn; [exact Hreftyped |reflexivity |reflexivity |apply ty_vali].
    - split; [exact Hreflocated |]. simpl; auto.
    - simpl; auto. }
  destruct (coherent_primitive_assignment_progress ge empty_context
    (PTree.set fresh execution_reference empty_stcontext) empty_vmap first execution_no_objects
    (extend_scalar_layout execution_no_cells fresh Ptrofs.zero execution_int BMint32) execution_no_packets
    p fresh Ptrofs.zero (Tint I32 Signed noattr) noattr (Vint (Int.repr 73)) [Write] Hwriteconfig)
    as [final [Hwrite [Hwritegrow [Hunit HcoherentFinal]]]].
  assert (Hstore : Mem.store Mint32 first fresh 0 (Values.Vint (Int.repr 73)) = Some final).
  { inversion Hwrite; subst; try solve [exfalso; eapply value_has_no_small_step; eauto].
    exact (primitive_assignment_to_store ge first final fresh Ptrofs.zero
      (Tint I32 Signed noattr) (Vint (Int.repr 73)) I ltac:(eassumption)). }
  assert (Hload : Mem.load Mint32 final fresh 0 = Some (Values.Vint (Int.repr 73))).
  { exact (Mem.load_store_same _ _ _ _ _ _ Hstore). }
  exists first, final, fresh. split; [exact Href |]. split; [exact Hwrite |]. split.
  - eapply ssem_deref2. eapply deref_addr_value with (chunk := BMint32) (v := Values.Vint (Int.repr 73));
      try reflexivity; exact Hload.
  - destruct Hunit as [HfinalHeap HunitTyped HunitLoc HunitFrames]. split; [|exact HcoherentFinal].
    constructor; [exact HfinalHeap |apply ty_vali |exact I |exact I].
Qed.

Print Assumptions coherent_reference_write_read_execution.
