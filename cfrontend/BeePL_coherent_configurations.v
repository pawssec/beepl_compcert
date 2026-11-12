Require Import BeePL_heap_extents BeePL_block_extents BeePL_storage_types.
(* A coherent layout rules out incompatible overlapping views. Primitive writes
   derive their target cell from the source reference's runtime location. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_soundness_arrays BeePL_callable_locations BeePL_aggregate_memory.
Require Import BeePL_object_coverage BeePL_initialized_runtime BeePL_initialized_mutation.
Require Import BeePL_layout_coherence BeePL_initialized_arrays BeePL_array_storage_typing.
Require Import BeePL_initialized_configurations BeePL_packet_bindings BeePL_packet_heap.
Import ListNotations.

Definition coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty : Prop :=
  initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty /\ coherent_layout cells.

Lemma primitive_reference_initialized_cell : forall ge Sigma m objects cells b ofs pt pa,
  initialized_object_memory ge Sigma m objects cells ->
  descriptor_heap_locations ge cells objects b ofs (Ptrtype (Reftype (Bprim pt) pa)) ->
  cells b ofs (Vtype pt) (chunk_of_ptype pt).
Proof.
  intros ge Sigma m objects cells b ofs pt pa Hmemory Hlocation.
  assert (Hcell : exists chunk, cells b ofs (Vtype pt) chunk).
  { destruct Hlocation as [Hcall | Hobject].
    - change (array_heap_locations ge.(genv_cenv) cells b ofs (Ptrtype (Reftype (Bprim pt) pa))) in Hcall.
      destruct Hcall as [Hscalar | [elem [len [a [Hbad Hrest]]]]]; [|discriminate Hbad].
      exact (scalar_reference_cell _ _ _ _ Hscalar).
    - destruct Hobject as [[Hbad _] | [basic [attr [Hty [Hkind Hentry]]]]]; [discriminate Hbad |].
      inversion Hty; subst. discriminate Hkind. }
  destruct Hcell as [chunk Hcell].
  pose proof (typed_cell_access _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
  pose proof (primitive_chunk_access pt) as Hcanonical.
  assert (Heq : transl_bchunk_cchunk chunk = transl_bchunk_cchunk (chunk_of_ptype pt)) by congruence.
  assert (Hchunk : chunk = chunk_of_ptype pt).
  { revert Heq. generalize (chunk_of_ptype pt). intros other Heq. destruct chunk, other; simpl in Heq; congruence. }
  subst chunk. exact Hcell.
Qed.

Theorem coherent_primitive_assignment_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype ->
  ssem_expr ge p vm m
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype)
    final vm' e' ->
  vm' = vm /\ e' = Val Vunit Utype /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil Utype /\
  sub_effect nil ef = true.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef final vm' e' [Hconfig Hcoherent] Hstep.
  pose proof Hconfig as [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyping [Hlocation Hrest] Hframes].
  pose proof (primitive_reference_initialized_cell _ _ _ _ _ _ _ _ _ Hmemory (packet_heap_locations_nonbytes _ _ _ _ _ _ (Ptrtype (Reftype (Bprim pt) pa)) ltac:(discriminate) Hlocation)) as Hcell.
  destruct (initialized_primitive_assignment_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfig Hcell (Hcoherent _ _ _ _ Hcell) Hstep) as [Hvm [He [Hevolve [Hfinal Hsub]]]].
  split; [exact Hvm |]. split; [exact He |]. split; [exact Hevolve |]. split; [split; assumption |exact Hsub].
Qed.

Theorem coherent_primitive_assignment_progress :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype) ef Utype ->
  exists final,
    ssem_expr ge p vm m
      (Prim Massgn [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa)); Val v (Vtype pt)] Utype)
      final vm (Val Vunit Utype) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm final objects cells packets (Val Vunit Utype) nil Utype.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef [Hconfig Hcoherent].
  pose proof Hconfig as [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyping [Hlocation Hrest] Hframes].
  pose proof (primitive_reference_initialized_cell _ _ _ _ _ _ _ _ _ Hmemory (packet_heap_locations_nonbytes _ _ _ _ _ _ (Ptrtype (Reftype (Bprim pt) pa)) ltac:(discriminate) Hlocation)) as Hcell.
  destruct (initialized_primitive_assignment_progress ge Gamma Sigma vm m objects cells packets p b ofs pt pa v ef
    Hconfig Hcell (Hcoherent _ _ _ _ Hcell)) as [final [Hstep [Hevolve Hfinal]]].
  exists final. split; [exact Hstep |]. split; [exact Hevolve |]. split; assumption.
Qed.

Print Assumptions primitive_reference_initialized_cell.
Print Assumptions coherent_primitive_assignment_preservation.
Print Assumptions coherent_primitive_assignment_progress.

Require Import BeePL_array_proofs BeePL_callable_variables.
Local Open Scope Z_scope.

Theorem coherent_array_configuration_preservation :
  forall ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  ssem_expr ge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm' e' ->
  exists Sigma' objects' cells',
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration ge Gamma Sigma' vm' final objects' cells' packets e' ef (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef final vm' e'
    [Hconfig Hcoherent] Hvalues Hstep.
  destruct (array_value_initializer_step_shape _ _ _ _ _ _ _ _ _ _ Hvalues Hstep)
    as [[Hm [Hvm He]] | [fresh He]].
  - subst final vm' e'. exists Sigma, objects, cells. split.
    + eapply initialized_heap_evolution_refl. exact (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hconfig).
    + split; assumption.
  - subst e'. destruct Hconfig as [[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes].
    destruct (typed_primitive_array_storage_conditions _ _ _ _ _ _ _ _ _ Htyped) as [Hvolatile Hbound].
    destruct (completed_initialized_array_preservation ge Gamma Sigma objects cells p vm m arr pt len attr
      es ef final vm' fresh Htyped Hvalues Hblocks Hmemory Hstep)
      as [Sigma' [HSigma [Hvm [Hext [Hblocks' [Hmemory' Htyped']]]]]].
    assert (Hpacket' : packet_heap_invariant ge Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) packets).
    { eapply completed_primitive_array_packets; eauto. }
    assert (Hextents' : heap_block_extents Sigma' final
      (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr))
      (extend_array_layout cells fresh pt (length es)) packets).
    { rewrite HSigma. eapply completed_array_extents; [exact Hextents| | |exact Hstep].
      - eapply storage_type_size_bounds. inversion Htyped; subst; assumption.
      - intros b ofs ty chunk [Hold|[i [Hi [Hb Hrest]]]]; [left; exact Hold|right; exact Hb]. }
    exists Sigma', (add_aggregate_descriptor objects fresh Ptrofs.zero (Atype (Vtype pt) len attr)),
      (extend_array_layout cells fresh pt (length es)).
    split.
    + constructor; try assumption; intros; try (left; assumption); assumption.
    + split.
      * constructor.
        -- constructor; try assumption. subst vm'. eapply packet_variable_layout_extend with (cells := cells) (objects := objects) (packets := packets);
          [exact Hext|intros; left; assumption|intros; left; assumption|intros; assumption|exact Hbindings].
        -- exact Htyped'.
        -- left; apply aggregate_descriptor_direct; [reflexivity |]. right; auto.
        -- exact I.
      * eapply completed_primitive_array_layout_coherent; eauto.
        exact (initialized_object_cells _ _ _ _ _ Hmemory).
Qed.

Theorem coherent_array_configuration_progress :
  forall ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  exists final fresh Sigma' objects' cells',
    ssem_expr ge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) final vm
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma' final objects' cells' packets /\
    coherent_runtime_configuration ge Gamma Sigma' vm final objects' cells' packets
      (Val (Vloc fresh Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr).
Proof.
  intros ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef Hinitial Hvalues.
  pose proof Hinitial as [[[Hblocks Hmemory Hbindings Hpacket Hextents] Htyped Hlocations Hframes] Hcoherent].
  destruct (initialized_array_progress ge Gamma Sigma objects cells p vm m arr pt len attr es ef
    Htyped Hvalues Hblocks Hmemory) as [final [fresh [allocated [Hstep Hrest]]]].
  destruct (coherent_array_configuration_preservation ge Gamma Sigma objects cells packets p vm m arr pt len attr es ef
    final vm _ Hinitial Hvalues Hstep) as [Sigma' [objects' [cells' [Hevolve Hfinal]]]].
  exists final, fresh, Sigma', objects', cells'. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions coherent_array_configuration_preservation.
Print Assumptions coherent_array_configuration_progress.
