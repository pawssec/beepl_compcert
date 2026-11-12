Require Import BeePL_heap_extents BeePL_block_extents.
Require Import BeePL_scalar_object_coherence BeePL_object_separation.
(* Relocating a coherent source layout into a fresh block preserves exact
   aliases and byte separation. This applies to scalar and pointer leaves. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_fresh_copy.
Require Import BeePL_aggregate_reference BeePL_initialized_reference.
Require Import BeePL_layout_coherence BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_callable_variables.
Require Import BeePL_auxlemmas.
Require Import BeePL_aggregate_copy BeePL_packet_copy BeePL_packet_heap BeePL_packet_bindings.
Require Import BeePL_packet_alignment.
Import ListNotations.
Local Open Scope Z_scope.

Theorem fresh_copy_layout_coherent : forall cells src start count fresh,
  coherent_layout cells ->
  (forall ofs ty chunk, ~ cells fresh ofs ty chunk) ->
  count <= Ptrofs.modulus ->
  coherent_layout (fresh_copy_layout cells src start count fresh).
Proof.
  intros cells src start count fresh Hcoherent Hfresh Hbound b ofs ty chunk Hcell old off t ch Hold.
  destruct Hcell as [Hcell | [Hb [source [delta [Hsource [Hsourceofs [Hdelta [Hlimit Hofs]]]]]]]];
    destruct Hold as [Hold | [Holdb [source' [delta' [Hsource' [Hsourceofs' [Hdelta' [Hlimit' Hoff]]]]]]]].
  - eapply Hcoherent; eauto.
  - subst old. right; left. intro Heq. subst b. eapply Hfresh; eauto.
  - subst b. right; left. intro Heq. subst old. eapply Hfresh; eauto.
  - subst b old ofs off.
    assert (Hrange : 0 <= delta <= Ptrofs.max_unsigned).
    { pose proof (size_chunk_pos (transl_bchunk_cchunk chunk)). unfold Ptrofs.max_unsigned. lia. }
    assert (Hrange' : 0 <= delta' <= Ptrofs.max_unsigned).
    { pose proof (size_chunk_pos (transl_bchunk_cchunk ch)). unfold Ptrofs.max_unsigned. lia. }
    destruct (Hcoherent _ _ _ _ Hsource _ _ _ _ Hsource')
      as [[Hb [Hoffset [Hty Hchunk]]] | [Hneq | [Hafter | Hbefore]]].
    + subst source' t ch. assert (delta' = delta) by lia. subst delta'. left; auto.
    + contradiction.
    + right; right; left. rewrite !Ptrofs.unsigned_repr by assumption. lia.
    + right; right; right. rewrite !Ptrofs.unsigned_repr by assumption. lia.
Qed.

Theorem allocated_fresh_copy_layout_coherent :
  forall cenv Sigma cells m allocated fresh src start count,
  coherent_layout cells -> typed_memory_layout cenv Sigma cells m ->
  Mem.alloc m 0 count = (allocated, fresh) -> count <= Ptrofs.modulus ->
  coherent_layout (fresh_copy_layout cells src start count fresh).
Proof.
  intros cenv Sigma cells m allocated fresh src start count Hcoherent Hmemory Halloc Hbound.
  apply fresh_copy_layout_coherent; try assumption.
  intros ofs ty chunk Hentry. eapply Mem.fresh_block_alloc; [exact Halloc |].
  eapply initialized_scalar_valid_block. eapply typed_memory_cell_erasure. apply Hmemory; exact Hentry.
Qed.

Lemma completed_aggregate_reference_layout_coherent :
  forall ge Sigma p vm m cells src base basic attr final vm' fresh,
  coherent_layout cells -> typed_memory_layout ge.(genv_cenv) Sigma cells m ->
  is_aggregate_type (construct_type_btype basic) = true ->
  sizeof_type ge.(genv_cenv) (construct_type_btype basic) <= Ptrofs.modulus ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    final vm' (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) ->
  coherent_layout (aggregate_reference_cells ge cells src base basic fresh).
Proof.
  intros ge Sigma p vm m cells src base basic attr final vm' fresh Hcoherent Hmemory Hkind Hbound Hstep.
  inversion Hstep; subst.
  - destruct basic; simpl in Hkind; try discriminate;
      match goal with H : chunk_of_type _ = Some _ |- _ => discriminate H end.
  - unfold aggregate_reference_cells. eapply allocated_fresh_copy_layout_coherent; eauto.
Qed.

Lemma completed_aggregate_reference_copy_effect :
  forall ge p vm m src base basic attr final vm' fresh,
  is_aggregate_type (construct_type_btype basic) = true ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    final vm' (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) ->
  exists allocated bytes,
    Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) = (allocated, fresh) /\
    Mem.loadbytes allocated src (Ptrofs.unsigned base) (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) = Some bytes /\
    Mem.storebytes allocated fresh 0 bytes = Some final.
Proof.
  intros ge p vm m src base basic attr final vm' fresh Hkind Hstep.
  inversion Hstep; subst.
  - destruct basic; simpl in Hkind; try discriminate;
      match goal with H : chunk_of_type _ = Some _ |- _ => discriminate H end.
  - match goal with Hassign : assign_addr _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (aggregate_assignment_bytes _ _ _ _ _ _ _ _ Hkind Hassign) as [bytes [Hr Hw]] end.
    rewrite Ptrofs.unsigned_zero in Hw. eexists; exists bytes; repeat split; eassumption.
Qed.

Theorem coherent_aggregate_reference_preservation :
  forall ge Gamma Sigma p vm m objects cells packets src base basic attr ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    ef (Ptrtype (Reftype basic attr)) ->
  objects src base (construct_type_btype basic) ->
  ge.(genv_cenv) = p.(prog_comp_env) ->
  ssem_expr ge p vm m
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr))) final vm' e' ->
  exists fresh,
    vm' = vm /\ e' = Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr)) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
      (aggregate_reference_cells ge cells src base basic fresh) (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh) /\
    coherent_runtime_configuration ge Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) vm' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
      (aggregate_reference_cells ge cells src base basic fresh) (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh) e' nil (Ptrtype (Reftype basic attr)) /\
    sub_effect nil ef = true.
Proof.
  intros ge Gamma Sigma p vm m objects cells packets src base basic attr ef final vm' e'
    [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyping Hlocations Hframes] Hcoherent] Hsource Henv Hstep.
  assert (Halign : relative_copy_alignment cells src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic))).
  { pose proof (initialized_object_scalar_coherence _ _ _ _ _ Hmemory) as Hscalar.
    pose proof (aggregate_object_readable _ _ _ _
      (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hsource) as Hreadable.
    rewrite Henv in Hscalar, Hreadable |- *.
    eapply coherent_object_relative_copy_alignment;
      [exact Hscalar|exact Hsource|exact (proj1 (proj2 Hreadable))]. }
  assert (HpacketAlign : packet_object_copy_alignment ge.(genv_cenv) (construct_type_btype basic)).
  { rewrite Henv. intros delta Hpath. eapply program_bytes_path_aligned; exact Hpath. }
  destruct (initialized_aggregate_reference_preservation ge p vm Sigma Gamma cells objects m src base basic attr
    final vm' e' Hmemory Hblocks Hsource Halign Hstep)
    as [fresh [Hvm [He [[Hext [Hblocks' Hmemory']] [Htyped' Hlocations']]]]].
  pose proof (aggregate_object_readable _ _ _ _ (initialized_object_descriptors _ _ _ _ _ Hmemory)
    _ _ _ Hsource) as [Hkind [Hsize [Hbound Hrest]]].
  assert (Hcoherent' : coherent_layout (aggregate_reference_cells ge cells src base basic fresh)).
  { subst e'. eapply completed_aggregate_reference_layout_coherent; eauto.
    - exact (initialized_object_cells _ _ _ _ _ Hmemory).
    - pose proof (Ptrofs.unsigned_range base). lia. }
  assert (Hpackets' : packet_heap_invariant ge (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma)
    final (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
    (aggregate_reference_cells ge cells src base basic fresh)
    (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh)).
  { destruct (completed_aggregate_reference_copy_effect _ _ _ _ _ _ _ _ _ _ _ Hkind
      ltac:(rewrite <- He; exact Hstep)) as [allocated [bytes [Halloc [Hread Hstore]]]].
    unfold aggregate_reference_cells. eapply fresh_object_copy_packet_heap;
      [exact (initialized_object_descriptors _ _ _ _ _ Hmemory)|exact Hsource|
       exact (initialized_object_cells _ _ _ _ _ Hmemory)|exact Hpackets|exact Hext| |exact HpacketAlign|
       exact Halloc|exact Hread|exact Hstore].
    replace 0 with (Ptrofs.unsigned Ptrofs.zero) by reflexivity.
    eapply aggregate_object_typing; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory')|].
    right; auto. }
  assert (Hextents' : heap_block_extents
    (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) final
    (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
    (aggregate_reference_cells ge cells src base basic fresh)
    (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh)).
  { destruct (completed_aggregate_reference_copy_effect _ _ _ _ _ _ _ _ _ _ _ Hkind
      ltac:(rewrite <- He; exact Hstep)) as [allocated [bytes [Halloc [Hread Hstore]]]].
    eapply heap_extents_storebytes; [|exact Hstore].
    eapply heap_extents_allocation; [exact Hextents|exact Halloc| |].
    - pose proof (aggregate_object_address_bound _ _ _ _
        (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hsource).
      pose proof (Ptrofs.unsigned_range base). lia.
    - eapply tracked_data_block_same_block_extension.
      + intros; eapply store_set_lookup_origin; eauto.
      + intros b ofs ty [Hold|[Hb HoriginRest]]; [left; exact Hold|right; exact Hb].
      + intros b ofs ty chunk [Hold|[Hb HoriginRest]]; [left; exact Hold|right; exact Hb].
      + intros b ofs [Hold|[Hb HoriginRest]]; [left; exact Hold|right; exact Hb]. }
  exists fresh. split; [exact Hvm |]. split; [exact He |]. split.
  - constructor; try assumption.
    + intros; apply fresh_copy_layout_extends; assumption.
    + intros; left; assumption.
    + intros; left; assumption.
  - split; [|apply sub_effect_nil]. split; [|exact Hcoherent']. constructor.
    + constructor; try assumption. subst vm'. eapply packet_variable_layout_extend with (cells := cells) (objects := objects) (packets := packets);
        [exact Hext|intros; apply fresh_copy_layout_extends; assumption|intros; left; assumption|intros; left; assumption|exact Hbindings].
    + exact Htyped'.
    + eapply runtime_locations_monotone; [apply packet_descriptor_embedding|exact Hlocations'].
    + subst e'. exact I.
Qed.

Print Assumptions fresh_copy_layout_coherent.
Print Assumptions coherent_aggregate_reference_preservation.

Theorem coherent_aggregate_reference_progress :
  forall ge Gamma Sigma p vm m objects cells packets src base basic attr ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    ef (Ptrtype (Reftype basic attr)) ->
  objects src base (construct_type_btype basic) ->
  ge.(genv_cenv) = p.(prog_comp_env) ->
  exists final fresh,
    ssem_expr ge p vm m
      (Prim Ref [Val (Vloc src base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    initialized_heap_evolution ge Sigma objects cells packets
      (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
      (aggregate_reference_cells ge cells src base basic fresh) (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh) /\
    coherent_runtime_configuration ge Gamma (PTree.set fresh (Ptrtype (Reftype basic attr)) Sigma) vm final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (construct_type_btype basic))
      (aggregate_reference_cells ge cells src base basic fresh) (copied_object_packets ge.(genv_cenv) packets (construct_type_btype basic) fresh)
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil (Ptrtype (Reftype basic attr)).
Proof.
  intros ge Gamma Sigma p vm m objects cells packets src base basic attr ef Hconfig Hsource Henv.
  pose proof Hconfig as [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyping Hlocations Hframes] Hcoherent].
  assert (Halign : relative_copy_alignment cells src (Ptrofs.unsigned base)
    (sizeof_type ge.(genv_cenv) (construct_type_btype basic))).
  { pose proof (initialized_object_scalar_coherence _ _ _ _ _ Hmemory) as Hscalar.
    pose proof (aggregate_object_readable _ _ _ _
      (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hsource) as Hreadable.
    rewrite Henv in Hscalar, Hreadable |- *.
    eapply coherent_object_relative_copy_alignment;
      [exact Hscalar|exact Hsource|exact (proj1 (proj2 Hreadable))]. }
  assert (Hbase : (alignof_blockcopy (bcomposite_composite_env ge.(genv_cenv))
    (transBeePL_type (construct_type_btype basic)) | Ptrofs.unsigned base)).
  { pose proof (aggregate_object_typing _ _ _ _
      (initialized_object_descriptors _ _ _ _ _ Hmemory) _ _ _ Hsource) as Hobject.
    rewrite Henv in Hobject |- *. eapply program_typed_object_copy_alignment; exact Hobject. }
  destruct (initialized_aggregate_reference_progress ge p vm Sigma Gamma cells objects m src base basic attr
    Hmemory Hblocks Hsource Hbase Halign) as [final [fresh [Hstep Hrest]]].
  destruct (coherent_aggregate_reference_preservation ge Gamma Sigma p vm m objects cells packets src base basic attr
    ef final vm _ Hconfig Hsource Henv Hstep) as [actual [_ [He [Hevolve [Hfinal Hsub]]]]].
  assert (actual = fresh) by congruence. subst actual.
  exists final, fresh. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions coherent_aggregate_reference_progress.
