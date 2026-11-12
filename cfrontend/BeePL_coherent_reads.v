Require Import BeePL_heap_extents.
(* Read heads obtain initialized cells/descriptors from their runtime operands.
   Scalar reads leave the coherent layout unchanged; aggregate indexing adds
   only a descriptor of an already initialized subobject. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_substitution_proofs.
Require Import BeePL_runtime_locations BeePL_callable_locations BeePL_soundness_arrays.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_covered_reads.
Require Import BeePL_aggregate_array_reads BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_packet_state BeePL_packet_bindings BeePL_packet_heap.
Require Import BeePL_packet_coverage BeePL_aggregate_array_elements.
Require Import BeePL_packet_object_layout.
Import ListNotations.

Theorem coherent_primitive_deref_progress :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa))] (Vtype pt)) ef (Vtype pt) ->
  exists v,
    ssem_expr ge p vm m
      (Prim Deref [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa))] (Vtype pt))
      m vm (Val v (Vtype pt)) /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v (Vtype pt)) nil (Vtype pt).
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa ef
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyped [Hlocation Hrest] Hframes] Hcoherent].
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  pose proof (primitive_reference_initialized_cell _ _ _ _ _ _ _ _ _ Hmemory Hlocation) as Hcell.
  destruct (typed_memory_cell_read ge.(genv_cenv) Gamma Sigma m b ofs (Vtype pt) (chunk_of_ptype pt)
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as [v [Hread Hvalue]].
  exists v. split; [apply ssem_deref2; exact Hread |]. split; [|exact Hcoherent].
  constructor; [constructor; assumption | exact Hvalue | |exact I].
  eapply value_locations_monotone; [apply packet_descriptor_embedding|].
  eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto.
Qed.

Theorem coherent_primitive_deref_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b ofs pt pa ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim Deref [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa))] (Vtype pt)) ef (Vtype pt) ->
  ssem_expr ge p vm m
    (Prim Deref [Val (Vloc b ofs) (Ptrtype (Reftype (Bprim pt) pa))] (Vtype pt)) final vm' e' ->
  final = m /\ vm' = vm /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' nil (Vtype pt).
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b ofs pt pa ef final vm' e'
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyped [Hlocation Hrest] Hframes] Hcoherent] Hstep.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  pose proof (primitive_reference_initialized_cell _ _ _ _ _ _ _ _ _ Hmemory Hlocation) as Hcell.
  pose proof (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell) as HcellTyped.
  inversion Hstep; subst; try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [exfalso; eapply aggregate_readable_not_by_value; [apply primitive_chunk_access | eassumption]].
  split; [reflexivity |]. split; [reflexivity |]. split; [|exact Hcoherent].
  constructor; [constructor; assumption | | |exact I].
  - eapply typed_memory_cell_read_preservation; eauto.
  - eapply value_locations_monotone; [apply packet_descriptor_embedding|].
    eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto.
Qed.

Lemma located_scalar_array_cell :
  forall ge Sigma m objects cells packets b base elem len attr n chunk,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets b base (Atype elem len attr) ->
  (n < Z.to_nat len)%nat ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  exists stored, cells b (aggregate_array_result ge base elem n) elem stored.
Proof.
  intros ge Sigma m objects cells packets b base elem len attr n chunk Hmemory Hlocation Hindex Hmode.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  destruct Hlocation as [Hcall | [[Hkind Hobject] | [basic [pa [Hbad Hrest]]]]]; [| |discriminate Hbad].
  - eapply array_heap_element_cell_at; eauto.
  - pose proof (covered_array_leaf _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hindex Hmode) as Hleaf.
    destruct (covered_leaf_cell_add _ _ _ _ _ _ _ _ _ _ _ Hmemory Hobject Hleaf) as [stored [Hcell Heq]].
    exists stored; exact Hcell.
Qed.

Lemma located_aggregate_array_object :
  forall ge Sigma m objects cells packets b base elem len attr n,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets b base (Atype elem len attr) ->
  (n < Z.to_nat len)%nat -> is_aggregate_type elem = true ->
  objects b base (Atype elem len attr).
Proof.
  intros ge Sigma m objects cells packets b base elem len attr n Hmemory Hlocation Hindex Hkind.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  destruct Hlocation as [Hcall | [[Haggregate Hobject] | [basic [pa [Hbad Hrest]]]]]; [|exact Hobject |discriminate Hbad].
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hcall Hindex) as [chunk Hcell].
  pose proof (typed_cell_access _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
  pose proof (by_value_type_not_aggregate _ _ Hmode). congruence.
Qed.

Theorem coherent_scalar_array_read_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  exists v,
    ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) m vm (Val v elem) /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v elem) ef elem.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent] Hmode.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex]. subst ef.
  destruct (located_scalar_array_cell _ _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex Hmode) as [stored Hcell].
  destruct (typed_memory_cell_read ge.(genv_cenv) Gamma Sigma m b _ elem stored
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as [v [Hread Htyped]].
  exists v. split; [eapply ssem_array_read_value; eauto |]. split; [|exact Hcoherent].
  constructor; [constructor; assumption |exact Htyped | |exact I].
  eapply value_locations_monotone; [apply packet_descriptor_embedding|].
  eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto.
Qed.

Theorem coherent_scalar_array_read_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  access_mode_type elem = By_value (transl_bchunk_cchunk chunk) ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) final vm' e' ->
  final = m /\ vm' = vm /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' ef elem.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk final vm' e'
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent] Hmode Hstep.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex]. subst ef.
  destruct (located_scalar_array_cell _ _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex Hmode) as [stored Hcell].
  pose proof (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell) as HcellTyped.
  inversion Hstep; subst; try discriminate Hmode;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [exfalso; eapply aggregate_readable_not_by_value; [exact Hmode | eassumption]].
  split; [reflexivity |]. split; [reflexivity |]. split; [|exact Hcoherent].
  constructor; [constructor; assumption | | |exact I].
  - eapply typed_memory_cell_read_preservation; eauto.
  - eapply value_locations_monotone; [apply packet_descriptor_embedding|].
    eapply (initialized_object_locations _ _ _ _ _ Hmemory); eauto.
Qed.

Theorem coherent_aggregate_array_read_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  is_aggregate_type elem = true ->
  let result := aggregate_array_result ge base elem n in
  let objects' := add_aggregate_descriptor objects b result elem in
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem)
    m vm (Val (Vloc b result) elem) /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm m objects' cells packets (Val (Vloc b result) elem) ef elem.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent] Hkind. cbn zeta.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex].
  pose proof (located_aggregate_array_object _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex Hkind) as Hobject.
  destruct (aggregate_array_read_progress ge Gamma Sigma objects cells p vm m b base elem len attr n ef
    Hmemory Hobject Hkind Htyping) as [Hstep [Hmemory' [Htyped Hlocated]]].
  destruct (aggregate_array_element_path _ _ _ _ _ _ _ _ _ _
    (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject Hindex)
    as [Hpath [Hraw Hoffset]].
  assert (Hpacketstate' : packet_heap_invariant ge Sigma m
    (add_aggregate_descriptor objects b (aggregate_array_result ge base elem n) elem) cells packets).
  { destruct Hpacketstate as [Hvalid HpacketTypes Hcoverage Hseparation HobjectCoherence].
    constructor; try assumption.
    - eapply packet_coverage_subobject_extension; eauto.
    - eapply packet_object_coherence_subobject_extension; eauto. }
  assert (Hbindings' : packet_variable_layout Gamma Sigma ge vm cells
    (add_aggregate_descriptor objects b (aggregate_array_result ge base elem n) elem) packets).
  { eapply packet_variable_layout_extend with
      (Sigma := Sigma) (cells := cells) (objects := objects) (packets := packets).
    - apply store_context_extends_refl.
    - intros; assumption.
    - intros; left; assumption.
    - intros; assumption.
    - exact Hbindings. }
  assert (Hextents' : heap_block_extents Sigma m
    (add_aggregate_descriptor objects b (aggregate_array_result ge base elem n) elem) cells packets).
  { eapply heap_extents_add_object; [exact Hextents|].
    right; right; left. exists base, (Atype elem len attr); exact Hobject. }
  split; [exact Hstep |]. split.
  - constructor; auto using store_context_extends_refl. intros; left; assumption.
  - split; [|exact Hcoherent]. constructor; [constructor; assumption |exact Htyped | |exact I].
    eapply value_locations_monotone; [apply packet_descriptor_embedding|exact Hlocated].
Qed.

Theorem coherent_aggregate_array_read_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  is_aggregate_type elem = true ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) final vm' e' ->
  let objects' := add_aggregate_descriptor objects b (aggregate_array_result ge base elem n) elem in
  final = m /\ vm' = vm /\
  initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects' cells packets e' ef elem.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef final vm' e'
    Hconfig Hkind Hstep. cbn zeta.
  pose proof Hconfig as [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent].
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex].
  pose proof (located_aggregate_array_object _ _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex Hkind) as Hobject.
  destruct (aggregate_array_read_preservation ge Gamma Sigma objects cells p vm m b base elem len attr n ef final vm' e'
    Hmemory Hobject Hkind Htyping Hstep) as [Hm [Hvm [He Hrest']]]. subst final vm' e'.
  destruct (coherent_aggregate_array_read_progress ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef Hconfig Hkind)
    as [_ [Hevolve Hfinal]]. split; [reflexivity |]. split; [reflexivity |]. split; assumption.
Qed.

Print Assumptions coherent_primitive_deref_preservation.
Print Assumptions coherent_scalar_array_read_preservation.
Print Assumptions coherent_aggregate_array_read_preservation.

Lemma located_bytes_array_object :
  forall ge Sigma m objects cells packets b base len attr n,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets b base (Atype Bytes len attr) ->
  (n < Z.to_nat len)%nat -> objects b base (Atype Bytes len attr).
Proof.
  intros ge Sigma m objects cells packets b base len attr n Hmemory Hlocation Hindex.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  destruct Hlocation as [Hcall | [[Hkind Hobject] | [basic [pa [Hbad Hrest]]]]];
    [|exact Hobject|discriminate Hbad].
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hcall Hindex) as [chunk Hcell].
  pose proof (typed_cell_access _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
  discriminate Hmode.
Qed.

Theorem coherent_bytes_array_read_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype Bytes len attr)] Bytes) ef Bytes ->
  exists address,
    ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype Bytes len attr)] Bytes)
      m vm (Val (Vloc b address) Bytes) /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
      (Val (Vloc b address) Bytes) ef Bytes.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base len attr n ef
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent].
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex].
  subst ef.
  pose proof (located_bytes_array_object _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex) as Hobject.
  destruct (covered_bytes_array_read_progress ge Gamma Sigma m objects packets b base len attr n p vm nil
    (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject
    (packet_heap_coverage _ _ _ _ _ _ Hpacketstate)
    (packet_heap_valid _ _ _ _ _ _ Hpacketstate) Htyping)
    as [Hentry [Hstep Hvalue]].
  eexists. split; [exact Hstep|]. split; [|exact Hcoherent].
  constructor; [constructor; assumption|exact Hvalue| |exact I].
  right; split; [reflexivity|exact Hentry].
Qed.

Theorem coherent_bytes_array_read_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype Bytes len attr)] Bytes) ef Bytes ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype Bytes len attr)] Bytes)
    final vm' next ->
  final = m /\ vm' = vm /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next ef Bytes.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' next
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent] Hstep.
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex].
  subst ef.
  pose proof (located_bytes_array_object _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex) as Hobject.
  destruct (covered_bytes_array_read_preservation ge Gamma Sigma m objects packets b base len attr n p vm nil
    final vm' next (initialized_object_descriptors _ _ _ _ _ Hmemory) Hobject
    (packet_heap_coverage _ _ _ _ _ _ Hpacketstate)
    (packet_heap_valid _ _ _ _ _ _ Hpacketstate) Htyping Hstep)
    as [Hm [Hvm [address [He [Hentry Hvalue]]]]].
  subst final vm' next. split; [reflexivity|]. split; [reflexivity|]. split; [|exact Hcoherent].
  constructor; [constructor; assumption|exact Hvalue| |exact I].
  right; split; [reflexivity|exact Hentry].
Qed.

Print Assumptions coherent_bytes_array_read_progress.
Print Assumptions coherent_bytes_array_read_preservation.

Lemma located_unit_array_object :
  forall ge Sigma m objects cells packets b base len attr n,
  initialized_object_memory ge Sigma m objects cells ->
  packet_heap_locations ge cells objects packets b base (Atype Utype len attr) ->
  (n < Z.to_nat len)%nat -> objects b base (Atype Utype len attr).
Proof.
  intros ge Sigma m objects cells packets b base len attr n Hmemory Hlocation Hindex.
  apply packet_heap_locations_nonbytes in Hlocation; [|discriminate].
  destruct Hlocation as [Hcall | [[Haggregate Hobject] | [basic [pa [Hbad Hrest]]]]]; [|exact Hobject |discriminate Hbad].
  destruct (array_heap_element_cell_at _ _ _ _ _ _ _ _ Hcall Hindex) as [chunk Hcell].
  pose proof (typed_cell_access _ _ _ _ _ _ _
    (initialized_object_cells _ _ _ _ _ Hmemory _ _ _ _ Hcell)) as Hmode.
  discriminate Hmode.
Qed.

Theorem coherent_unit_array_read_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype Utype len attr)] Utype) ef Utype ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype Utype len attr)] Utype)
    m vm (Val Vunit Utype) /\
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val Vunit Utype) ef Utype.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base len attr n ef
    [[[Hblocks Hmemory Hbindings Hpacketstate Hextents] Htyping [Hlocation Hrest] Hframes] Hcoherent].
  destruct (typed_array_value_read_bound _ _ _ _ _ _ _ _ _ _ Htyping) as [Hef Hindex]. subst ef.
  pose proof (located_unit_array_object _ _ _ _ _ _ _ _ _ _ _ Hmemory Hlocation Hindex) as Hobject.
  split.
  - apply ssem_array_read_unit; [exact Hindex |].
    eapply aggregate_object_readable; [exact (initialized_object_descriptors _ _ _ _ _ Hmemory) |exact Hobject].
  - split; [|exact Hcoherent]. constructor; [constructor; assumption |constructor |exact I |exact I].
Qed.

Theorem coherent_unit_array_read_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' e',
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype Utype len attr)] Utype) ef Utype ->
  ssem_expr ge p vm m (Prim (ArrayRead n) [Val (Vloc b base) (Atype Utype len attr)] Utype) final vm' e' ->
  final = m /\ vm' = vm /\ e' = Val Vunit Utype /\
  coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets e' ef Utype.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' e' Hconfig Hstep.
  pose proof (proj2 (coherent_unit_array_read_progress ge Gamma Sigma vm m objects cells packets p b base len attr n ef Hconfig)) as Hfinal.
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try solve [match goal with H : deref_addr Utype _ _ _ _ _ |- _ => inversion H; discriminate end];
    try solve [match goal with H : aggregate_readable _ _ _ _ Utype |- _ => destruct H as [Hkind _]; discriminate end].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |exact Hfinal].
Qed.

Print Assumptions coherent_unit_array_read_progress.
Print Assumptions coherent_unit_array_read_preservation.
