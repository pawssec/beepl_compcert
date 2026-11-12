Require Import BeePL_heap_extents BeePL_block_extents BeePL_storage_types BeePL_initialized_configurations.
(* Unit-array initialization allocates identity/extent, but adds no scalar cells.
   Therefore it preserves initialized contents and layout coherence exactly. *)
Require Import List Bool ZArith Lia Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_array_proofs BeePL_initializer_frames BeePL_unit_arrays.
Require Import BeePL_structure_proofs.
Require Import BeePL_scalar_object_layout.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_fresh_copy.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_callable_variables.
Require Import BeePL_type_equality BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.
Local Open Scope Z_scope.

Lemma unit_value_arguments : forall cenv Gamma Sigma es ef ts,
  type_exprs cenv Gamma Sigma es ef ts ->
  Forall (fun e => exists v t, e = Val v t) es ->
  all_eq_type Utype ts = true ->
  Forall (fun v => v = Vunit) (extract_values_exprs es).
Proof.
  intros cenv Gamma Sigma es ef ts Htyped. induction Htyped; intros Hvalues Hequal; [constructor |].
  inversion Hvalues; subst.
  match goal with H : exists v t, e = Val v t |- _ => destruct H as [v [annotation He]]; subst e end.
  simpl in Hequal. apply andb_true_iff in Hequal as [Hhead Htail].
  change (eq_type Utype t = true) in Hhead.
  apply eq_type_sound in Hhead. subst t. inversion H; subst.
  simpl. constructor; [reflexivity |apply IHHtyped; assumption].
Qed.

Lemma typed_unit_array_arguments : forall cenv Gamma Sigma arr len attr es ef,
  type_expr cenv Gamma Sigma (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) ef (Atype Utype len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  len = Z.of_nat (length (extract_values_exprs es)) /\
  Forall (fun v => v = Vunit) (extract_values_exprs es) /\ ef = nil.
Proof.
  intros cenv Gamma Sigma arr len attr es ef Htyped Hvalues.
  pose proof (typed_array_initializer_extent _ _ _ _ _ _ _ _ Htyped) as [_ [elem [a Hextent]]].
  inversion Hextent. split.
  - rewrite extracted_value_arguments_length by exact Hvalues. congruence.
  - inversion Htyped; subst.
    match goal with Hget : get_array_elm_ty _ = OK _ |- _ => simpl in Hget; inversion Hget; subst end.
    split; [eapply unit_value_arguments; eauto |eapply value_arguments_effect_nil; eauto].
Qed.

Theorem unit_array_initialized_objects :
  forall ge Gamma Sigma objects cells arr len attr vs vm m vm' final Sigma',
  sem_array_init ge Sigma arr (Atype Utype len attr) vs vm m vm' final Sigma' ->
  initialized_object_memory ge Sigma m objects cells -> store_blocks_valid Sigma m ->
  exists fresh,
    PTree.get arr vm' = Some (fresh, Atype Utype len attr) /\
    store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype Utype len attr)) cells /\
    type_expr ge.(genv_cenv) Gamma Sigma'
      (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr)) nil (Atype Utype len attr).
Proof.
  intros ge Gamma Sigma objects cells arr len attr vs vm m vm' final Sigma'
    Hinit [Hobjects Hcoverage Htyped Hlocated HscalarCoherence] Hblocks.
  destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hinit)
    as [allocated [fresh [Halloc [Hlookup [Hhelper [Hlen [HS Hvm]]]]]]].
  pose proof (unit_array_elements_identity _ _ _ _ _ _ Hhelper) as Hfinal. subst final.
  destruct (array_initialization_store_typing ge ge.(genv_cenv) Gamma Sigma arr Utype len attr vs
    vm m vm' allocated Sigma' Hinit Hblocks ltac:(simpl; lia))
    as [actual [Hlookup' [Hext [Hblocks' Hvalue]]]].
  assert (actual = fresh) by congruence. subst actual.
  assert (Hcells : typed_memory_layout ge.(genv_cenv) Sigma' cells allocated).
  { eapply typed_memory_layout_context_extension; [|exact Hext].
    intros b ofs ty chunk Hentry. eapply typed_memory_cell_alloc_frame; eauto. }
  assert (HoldObjects : aggregate_objects_valid ge.(genv_cenv) Sigma' allocated objects).
  { eapply aggregate_objects_valid_frame; [exact Hobjects |exact Hext | |].
    - intros; eapply Mem.valid_block_alloc; eauto.
    - intros; eapply Mem.perm_alloc_1; eauto. }
  exists fresh. split; [exact Hlookup |]. split; [exact Hext |]. split; [exact Hblocks' |]. split; [|exact Hvalue].
  constructor.
  - destruct HoldObjects as [HoldTyping HoldReadable HoldAddress]. constructor; intros b base ty [Hold | [Hb [Hbase Hty]]].
    + apply HoldTyping; exact Hold.
    + subst. eapply array_location_typing_entry; exact Hvalue.
    + apply HoldReadable; exact Hold.
    + subst. eapply fresh_aggregate_readable; [reflexivity | |exact Halloc].
      change (0 <= 0 <= Ptrofs.modulus). pose proof Ptrofs.modulus_pos; lia.
    + eapply HoldAddress; exact Hold.
    + subst. rewrite Ptrofs.unsigned_zero. change (0 <= Ptrofs.max_unsigned).
      unfold Ptrofs.max_unsigned. pose proof Ptrofs.modulus_pos; lia.
  - intros b base root [Hold | [Hb [Hbase Hty]]] delta ty chunk Hleaf.
    + eapply Hcoverage; eauto.
    + subst. exfalso. eapply unit_array_no_scalar_leaf; exact Hleaf.
  - exact Hcells.
  - intros b ofs ty chunk Hentry v Hread.
    eapply value_locations_monotone with (L := descriptor_heap_locations ge cells objects).
    + apply descriptor_heap_locations_monotone; [auto |intros; left; assumption].
    + exact (allocation_memory_locations ge.(genv_cenv) Sigma
        (descriptor_heap_locations ge cells objects) cells m allocated fresh 0
        (sizeof_type ge.(genv_cenv) (Atype Utype len attr)) Htyped Hlocated Halloc
        b ofs ty chunk Hentry v Hread).
  - eapply scalar_object_coherence_fresh_descriptor; [exact Htyped|exact HscalarCoherence|].
    eapply Mem.fresh_block_alloc; exact Halloc.
Qed.

Theorem completed_unit_array_initialized_preservation :
  forall ge Gamma Sigma objects cells p vm m arr len attr es ef final vm' fresh,
  type_expr ge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) ef (Atype Utype len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  store_blocks_valid Sigma m -> initialized_object_memory ge Sigma m objects cells ->
  ssem_expr ge p vm m (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) final vm'
    (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr)) ->
  exists Sigma', Sigma' = PTree.set fresh (Atype Utype len attr) Sigma /\
    vm' = vm /\ store_context_extends Sigma Sigma' /\ store_blocks_valid Sigma' final /\
    initialized_object_memory ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype Utype len attr)) cells /\
    type_expr ge.(genv_cenv) Gamma Sigma'
      (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr)) ef (Atype Utype len attr).
Proof.
  intros ge Gamma Sigma objects cells p vm m arr len attr es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep.
  destruct (typed_unit_array_arguments _ _ _ _ _ _ _ _ Htyped Hvalues) as [Hlength [Hshapes Hef]]. subst ef.
  inversion Hstep; subst.
  match goal with Hinit : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (array_initialization_rebase _ _ _ _ _ _ _ _ _ _ Hinit Sigma) as [postSigma Hreal]
  end.
  destruct (unit_array_initialized_objects ge Gamma Sigma objects cells arr _ attr (extract_values_exprs es)
    _ m _ final postSigma Hreal Hmemory Hblocks) as [actual [Hlookup [Hext [Hblocks' [Hstate Hvalue]]]]].
  assert (actual = fresh) by congruence. subst actual.
  destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hreal)
    as [allocated [actual [Ha [Hlookup' [Hhelper [Hlen [HS Hvm]]]]]]].
  assert (actual=fresh) by congruence. subst actual.
  exists postSigma. split; [exact HS|]. split; [reflexivity |]. split; [exact Hext |]. split; [exact Hblocks' |]. split; assumption.
Qed.

Theorem coherent_unit_array_preservation :
  forall ge Gamma Sigma objects cells packets p vm m arr len attr es ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) ef (Atype Utype len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) final vm' e' ->
  exists Sigma' objects',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells packets e' ef (Atype Utype len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr len attr es ef final vm' e' [Hconfig Hcoherent] Hvalues Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]].
  - subst. exists Sigma, objects. split.
    + eapply initialized_heap_evolution_refl. exact (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hconfig).
    + split; assumption.
  - subst e'. destruct Hconfig as [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes].
    destruct (completed_unit_array_initialized_preservation ge Gamma Sigma objects cells p vm m arr len attr
      es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep)
      as [Sigma' [HSigma [Hvm [Hext [Hblocks' [Hmemory' Htyped']]]]]].
    assert (Hpacket' : packet_heap_invariant ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype Utype len attr)) cells packets).
    { inversion Hstep; subst.
      match goal with Hi : sem_array_init _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct (array_initialization_allocation_shape _ _ _ _ _ _ _ _ _ _ _ _ Hi)
          as [allocated [actual [Ha [Hlookup [Hhelper Hrest]]]]]
      end.
      assert (actual=fresh) by congruence. subst actual.
      eapply packet_heap_fresh_array_elements; eauto.
      apply unit_array_has_no_bytes_leaf. }
    assert (Hextents' : heap_block_extents Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype Utype len attr)) cells packets).
    { rewrite HSigma. eapply completed_array_extents; [exact Hextents| | |exact Hstep].
      - eapply storage_type_size_bounds. inversion Htyped; subst; assumption.
      - intros; left; assumption. }
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype Utype len attr)). split.
    + constructor; auto. intros; left; assumption.
    + split; [|exact Hcoherent]. constructor.
      * constructor; try assumption. subst vm'. eapply packet_variable_layout_extend with (cells := cells) (objects := objects) (packets := packets);
          [exact Hext|intros; assumption|intros; left; assumption|intros; assumption|exact Hbindings].
      * exact Htyped'.
      * left; apply aggregate_descriptor_direct; [reflexivity |]. right; auto.
      * exact I.
Qed.

Theorem coherent_unit_array_progress :
  forall ge Gamma Sigma objects cells packets p vm m arr len attr es ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) ef (Atype Utype len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  exists final fresh Sigma' objects',
    ssem_expr ge p vm m (Ainit arr (Atype Utype len attr) es (Atype Utype len attr)) final vm
      (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr)) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma' vm final objects' cells packets
      (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr)) ef (Atype Utype len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr len attr es ef Hconfig Hvalues.
  pose proof Hconfig as [[[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes] Hcoherent].
  destruct (typed_unit_array_arguments _ _ _ _ _ _ _ _ Htyped Hvalues) as [Hlength [Hshapes Hef]].
  destruct (unit_array_initialization_total ge Sigma vm m arr attr (extract_values_exprs es) Hshapes)
    as [allocated [fresh [Halloc [Hinit Hreadable]]]].
  rewrite <- Hlength in Hinit.
  assert (Hstep : ssem_expr ge p vm m (Ainit arr (Atype Utype len attr) es (Atype Utype len attr))
    allocated vm (Val (Vloc fresh Ptrofs.zero) (Atype Utype len attr))).
  { eapply ssem_array_init3; [exact Hvalues |exact Hinit |apply PTree.gss]. }
  destruct (coherent_unit_array_preservation ge Gamma Sigma objects cells packets p vm m arr len attr es ef
    allocated vm _ Hconfig Hvalues Hstep) as [Sigma' [objects' [Hevolve Hfinal]]].
  exists allocated, fresh, Sigma', objects'. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions unit_array_initialized_objects.
Print Assumptions coherent_unit_array_progress.
Print Assumptions coherent_unit_array_preservation.
