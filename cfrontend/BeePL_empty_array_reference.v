(* Empty callable arrays need no synthetic source object registration. Ref
   allocates a genuine empty block and performs the actual zero-byte copy. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_aggregate_copy BeePL_fresh_aggregate_memory.
Require Import BeePL_fresh_copy BeePL_object_coverage BeePL_array_object_coverage.
Require Import BeePL_scalar_object_layout BeePL_packet_heap BeePL_packet_bindings BeePL_packet_state.
Require Import BeePL_layout_coherence.
Require Import BeePL_block_extents.
Require Import BeePL_heap_extents BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_copy BeePL_callable_array_objects BeePL_object_separation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fresh_empty_array_reference_configuration :
  forall ge Gamma Sigma vm m objects cells packets pt attr pa allocated final fresh,
  initialized_heap_state ge Gamma Sigma vm m objects cells packets -> coherent_layout cells ->
  Mem.alloc m 0 0 = (allocated,fresh) -> Mem.storebytes allocated fresh 0 [] = Some final ->
  let ty := Atype (Vtype pt) 0 attr in
  let reference := Ptrtype (Reftype (Barray pt 0 attr) pa) in
  let Sigma' := PTree.set fresh reference Sigma in
  let objects' := add_aggregate_descriptor objects fresh Ptrofs.zero ty in
  initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells packets /\
  coherent_runtime_configuration ge Gamma Sigma' vm final objects' cells packets
    (Val (Vloc fresh Ptrofs.zero) reference) nil reference.
Proof.
  intros ge Gamma Sigma vm m objects cells packets pt attr pa allocated final fresh
    [Hblocks Hmemory Hbindings Hpackets Hextents] Hcoherent Halloc Hstore ty reference Sigma' objects'.
  assert (Hsize : sizeof_type ge.(genv_cenv) ty=0) by (change (sizeof_ptype pt*0=0); apply Z.mul_0_r).
  assert (HallocTyped : Mem.alloc m 0 (sizeof_type ge.(genv_cenv) ty)=(allocated,fresh))
    by (rewrite Hsize; exact Halloc).
  destruct (fresh_reference_aggregate_descriptors ge.(genv_cenv) Sigma m objects
    (Barray pt 0 attr) pa allocated fresh (initialized_object_descriptors _ _ _ _ _ Hmemory)
    Hblocks eq_refl ltac:(change (0<=sizeof_type ge.(genv_cenv) ty<=Ptrofs.max_unsigned); rewrite Hsize; vm_compute; intuition discriminate) HallocTyped)
    as [Hext [HblocksAllocated HobjectsAllocated]].
  assert (HblocksFinal : store_blocks_valid Sigma' final).
  { intros b t Hget. eapply Mem.storebytes_valid_block_1; [exact Hstore|]. exact (HblocksAllocated b t Hget). }
  assert (HcopyAlign : relative_copy_alignment cells fresh 0 0).
  { intros ofs t chunk delta Hcell Hofs Hd Hbound. pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)); lia. }
  destruct (fresh_copy_preserves_cells ge.(genv_cenv) Sigma
    (descriptor_heap_locations ge cells objects) cells m allocated final fresh fresh 0 0 []
    (initialized_object_cells _ _ _ _ _ Hmemory) (initialized_object_locations _ _ _ _ _ Hmemory)
    Halloc ltac:(pose proof Ptrofs.modulus_pos; lia) HcopyAlign
    ltac:(apply Mem.loadbytes_empty; lia) Hstore) as [HcopyCells HcopyLocations].
  assert (HcellsFinal : typed_memory_layout ge.(genv_cenv) Sigma' cells final).
  { eapply typed_memory_layout_context_extension; [|exact Hext].
    intros b ofs t chunk Hcell. apply HcopyCells; left; exact Hcell. }
  assert (HmemoryFinal : initialized_object_memory ge Sigma' final objects' cells).
  { constructor.
    - eapply aggregate_objects_valid_storebytes; eauto.
    - intros b base root [Hold|[Hb [Hbase Hty]]] delta t chunk Hleaf.
      + eapply (initialized_object_leaves _ _ _ _ _ Hmemory); eauto.
      + subst b base root. destruct (primitive_array_scalar_leaf _ _ _ _ _ _ _ Hleaf)
          as [i [Hi Hrest]]; lia.
    - exact HcellsFinal.
    - intros b ofs t chunk Hcell v Hread. eapply value_locations_monotone
        with (L := descriptor_heap_locations ge cells objects).
      + apply descriptor_heap_locations_monotone; [auto|intros; left; assumption].
      + eapply HcopyLocations; [left; exact Hcell|exact Hread].
    - eapply scalar_object_coherence_fresh_descriptor;
        [exact (initialized_object_cells _ _ _ _ _ Hmemory)|
         exact (initialized_object_scalar_coherence _ _ _ _ _ Hmemory)|].
      eapply Mem.fresh_block_alloc; exact Halloc. }
  assert (HpacketsAllocated : packet_heap_invariant ge Sigma' allocated objects' cells packets).
  { eapply packet_heap_fresh_array_elements with (base := Ptrofs.zero) (values := []) (elem := Vtype pt);
      [exact Hpackets|exact Hext|exact Halloc|constructor|apply primitive_array_has_no_bytes_leaf|auto]. }
  assert (HpacketsFinal : packet_heap_invariant ge Sigma' final objects' cells packets).
  { eapply packet_heap_storebytes_frame; [exact HpacketsAllocated| |exact Hstore].
    apply packet_block_disjoint_write. eapply allocated_packet_block_disjoint;
      [exact (packet_heap_valid _ _ _ _ _ _ Hpackets)|exact Halloc]. }
  assert (HextentsFinal : heap_block_extents Sigma' final objects' cells packets).
  { eapply heap_extents_storebytes; [|exact Hstore].
    eapply heap_extents_allocation; [exact Hextents|exact Halloc| |].
    - vm_compute; intuition discriminate.
    - eapply tracked_data_block_same_block_extension.
      + intros; eapply store_set_lookup_origin; eauto.
      + intros b ofs t [Hold|[Hb Hrest]]; [left; exact Hold|right; exact Hb].
      + intros; left; assumption.
      + intros; left; assumption. }
  split.
  - constructor; try assumption; intros; try (left; assumption); assumption.
  - split; [|exact Hcoherent]. constructor.
    + constructor; try assumption. eapply packet_variable_layout_extend;
        [exact Hext| | | |exact Hbindings]; intros; try (left; assumption); assumption.
    + apply ty_valloc; unfold Sigma'; apply PTree.gss.
    + left. apply aggregate_descriptor_reference; [reflexivity|right; auto].
    + exact I.
Qed.

Theorem empty_callable_array_reference_progress :
  forall ge Gamma Sigma p vm m objects cells packets source base pt attr pa ef,
  ge.(genv_cenv)=p.(prog_comp_env) ->
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc source base) (Atype (Vtype pt) 0 attr)]
      (Ptrtype (Reftype (Barray pt 0 attr) pa))) ef (Ptrtype (Reftype (Barray pt 0 attr) pa)) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val (Vloc source base) (Atype (Vtype pt) 0 attr)]
        (Ptrtype (Reftype (Barray pt 0 attr) pa))) final vm
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Barray pt 0 attr) pa))) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype (Barray pt 0 attr) pa)) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) 0 attr)) cells packets /\
    coherent_runtime_configuration ge Gamma
      (PTree.set fresh (Ptrtype (Reftype (Barray pt 0 attr) pa)) Sigma) vm final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) 0 attr)) cells packets
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Barray pt 0 attr) pa))) nil
      (Ptrtype (Reftype (Barray pt 0 attr) pa)).
Proof.
  intros ge Gamma Sigma p vm m objects cells packets source base pt attr pa ef Henv
    [[Hheap Htyping Hlocations Hframes] Hcoherent].
  destruct Hheap as [Hblocks Hmemory Hbindings Hpackets Hextents] eqn:HheapEq.
  assert (Hobject : object_type_at ge.(genv_cenv) Sigma source (Ptrofs.unsigned base) (Atype (Vtype pt) 0 attr)).
  { inversion Htyping; subst. match goal with Hv : type_expr _ _ _ (Val _ _) _ _ |- _ => inversion Hv; subst; assumption end. }
  assert (Htracked : tracked_data_block Sigma objects cells packets source).
  { left; eapply typed_data_object_store_origin; [exact Hobject|reflexivity]. }
  destruct (heap_extent_lookup _ _ _ _ _ _ Hextents Htracked) as [limit Hextent].
  assert (Hreadable : aggregate_readable ge.(genv_cenv) m source base (Atype (Vtype pt) 0 attr)).
  { assert (Hsize : sizeof_type ge.(genv_cenv) (Atype (Vtype pt) 0 attr)=0) by (change (sizeof_ptype pt*0=0); apply Z.mul_0_r).
    unfold aggregate_readable. rewrite Hsize.
    split; [reflexivity|]. split; [lia|]. split; [pose proof (Ptrofs.unsigned_range base); lia|].
    split; [exact (source_extent_valid _ _ _ Hextent)|intros ofs Hrange; lia]. }
  assert (Halign : (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv))
    (transBeePL_type (Atype (Vtype pt) 0 attr)) | Ptrofs.unsigned base)).
  { rewrite Henv in Hobject |- *. eapply program_typed_object_copy_alignment; exact Hobject. }
  destruct (Mem.alloc m 0 0) as [allocated fresh] eqn:Halloc.
  assert (HallocTyped : Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Atype (Vtype pt) 0 attr))=(allocated,fresh)).
  { change (Mem.alloc m 0 (sizeof_ptype pt*0)=(allocated,fresh)). rewrite Z.mul_0_r; exact Halloc. }
  pose proof (fresh_aggregate_copy_ready _ _ _ _ _ _ _ HallocTyped Hreadable Halign) as Hready.
  destruct (aggregate_assignment_progress _ _ _ _ _ _ _ Hready) as [final Hassign].
  destruct (aggregate_assignment_bytes _ _ (Atype (Vtype pt) 0 attr) _ _ _ _ _ eq_refl Hassign) as [bytes [Hload Hstore]].
  change (Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_ptype pt*0)=Some bytes) in Hload.
  rewrite Z.mul_0_r, Mem.loadbytes_empty in Hload by lia. inversion Hload; subst bytes.
  exists final, fresh. split.
  - eapply ssem_ref_aggregate with (basic := Barray pt 0 attr); [reflexivity|exact HallocTyped|exact Hassign].
  - eapply fresh_empty_array_reference_configuration; [exact Hheap|exact Hcoherent|exact Halloc|exact Hstore].
Qed.

Lemma empty_array_reference_step :
  forall ge p vm m source base pt attr pa final vm' e',
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc source base) (Atype (Vtype pt) 0 attr)]
      (Ptrtype (Reftype (Barray pt 0 attr) pa))) final vm' e' ->
  exists allocated fresh, vm'=vm /\
    e'=Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Barray pt 0 attr) pa)) /\
    Mem.alloc m 0 0=(allocated,fresh) /\ Mem.storebytes allocated fresh 0 []=Some final.
Proof.
  intros * Hstep. inversion Hstep; subst.
  - exfalso; eapply value_has_no_small_step; eauto.
  - match goal with Hchunk : chunk_of_type _ = Some _ |- _ => discriminate Hchunk end.
  - match goal with Ha : Mem.alloc m _ _ = (?allocated, ?fresh),
      Hass : assign_addr _ _ _ _ _ _ _ _ _ |- _ =>
      exists allocated, fresh; split; [reflexivity|]; split; [reflexivity|]; split;
      [change (Mem.alloc m 0 (sizeof_ptype pt*0)=(allocated,fresh)) in Ha;
       rewrite Z.mul_0_r in Ha; exact Ha|
       destruct (aggregate_assignment_bytes _ _ (Atype (Vtype pt) 0 attr) _ _ _ _ _ eq_refl Hass) as [bytes [Hload Hstore]]]
    end.
    change (Mem.loadbytes allocated source (Ptrofs.unsigned base) (sizeof_ptype pt*0)=Some bytes) in Hload.
    rewrite Z.mul_0_r, Mem.loadbytes_empty in Hload by lia. inversion Hload; subst bytes. exact Hstore.
Qed.

Theorem empty_callable_array_reference_preservation :
  forall ge Gamma Sigma p vm m objects cells packets source base pt attr pa ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc source base) (Atype (Vtype pt) 0 attr)]
      (Ptrtype (Reftype (Barray pt 0 attr) pa))) ef (Ptrtype (Reftype (Barray pt 0 attr) pa)) ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc source base) (Atype (Vtype pt) 0 attr)]
      (Ptrtype (Reftype (Barray pt 0 attr) pa))) final vm' e' ->
  exists fresh,
    vm'=vm /\ e'=Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype (Barray pt 0 attr) pa)) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype (Barray pt 0 attr) pa)) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) 0 attr)) cells packets /\
    coherent_runtime_configuration ge Gamma
      (PTree.set fresh (Ptrtype (Reftype (Barray pt 0 attr) pa)) Sigma) vm' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) 0 attr)) cells packets e' nil
      (Ptrtype (Reftype (Barray pt 0 attr) pa)).
Proof.
  intros * [[Hheap Htyping Hlocations Hframes] Hcoherent] Hstep.
  destruct (empty_array_reference_step _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as [allocated [fresh [Hvm [He [Halloc Hstore]]]]].
  subst vm' e'. exists fresh. split; [reflexivity|]. split; [reflexivity|].
  eapply fresh_empty_array_reference_configuration; eauto.
Qed.

Print Assumptions empty_callable_array_reference_progress.
Print Assumptions empty_callable_array_reference_preservation.
