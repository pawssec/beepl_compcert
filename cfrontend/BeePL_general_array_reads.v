(* The read guard excludes the one element kind with no operational read.
   All remaining element kinds use the shared initialized heap invariant. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_memory BeePL_aggregate_memory BeePL_packet_state.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_coherent_reads.
Import ListNotations.

Lemma readable_array_element_cases : forall ty,
  is_funtype ty = false ->
  ty = Utype \/
  (exists chunk, access_mode_type ty = By_value (transl_bchunk_cchunk chunk)) \/
  is_aggregate_type ty = true \/ ty = Bytes.
Proof.
  intros ty Hdata. destruct ty; try discriminate; auto.
  - right; left. exists (chunk_of_ptype p). apply primitive_chunk_access.
  - right; left. simpl. unfold Mptr. destruct Archi.ptr64;
      [exists BMint64 | exists BMint32]; reflexivity.
Qed.

Lemma typed_array_read_element_supported : forall env Gamma Sigma e ef elem len attr n,
  type_expr env Gamma Sigma
    (Prim (ArrayRead n) [e] elem) ef elem ->
  type_expr env Gamma Sigma e ef (Atype elem len attr) ->
  is_funtype elem = false.
Proof. intros * Hread Harray. inversion Hread; subst; assumption. Qed.

Theorem coherent_general_array_read_progress :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  exists value objects',
    ssem_expr ge p vm m
      (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem)
      m vm (Val value elem) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects' cells packets
      (Val value elem) ef elem.
Proof.
  intros * Hconfig.
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
  assert (Hdata : is_funtype elem = false) by (inversion Htyped; subst; assumption).
  destruct (readable_array_element_cases elem Hdata) as [Hunit | [[chunk Hmode] | [Haggregate | Hbytes]]].
  - subst elem. destruct (coherent_unit_array_read_progress ge Gamma Sigma vm m objects cells packets p b base len attr n ef Hconfig)
      as [Hstep Hfinal].
    exists Vunit, objects. split; [exact Hstep |]. split; [|exact Hfinal].
    eapply initialized_heap_evolution_refl; exact Hheap.
  - destruct (coherent_scalar_array_read_progress ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk Hconfig Hmode)
      as [v [Hstep Hfinal]].
    exists v, objects. split; [exact Hstep |]. split; [|exact Hfinal].
    eapply initialized_heap_evolution_refl; exact Hheap.
  - destruct (coherent_aggregate_array_read_progress ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef Hconfig Haggregate)
      as [Hstep [Hevolve Hfinal]].
    do 2 eexists. split; [exact Hstep |]. split; [exact Hevolve |exact Hfinal].
  - subst elem. destruct (coherent_bytes_array_read_progress ge Gamma Sigma vm m objects cells packets p b base len attr n ef Hconfig)
      as [address [Hstep Hfinal]].
    exists (Vloc b address), objects. split; [exact Hstep |]. split; [|exact Hfinal].
    eapply initialized_heap_evolution_refl; exact Hheap.
Qed.

Theorem coherent_general_array_read_preservation :
  forall ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) ef elem ->
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b base) (Atype elem len attr)] elem) final vm' next ->
  final = m /\ vm' = vm /\
  exists objects',
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects' cells packets next ef elem.
Proof.
  intros * Hconfig Hstep.
  pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
  assert (Hdata : is_funtype elem = false) by (inversion Htyped; subst; assumption).
  destruct (readable_array_element_cases elem Hdata) as [Hunit | [[chunk Hmode] | [Haggregate | Hbytes]]].
  - subst elem.
    destruct (coherent_unit_array_read_preservation ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' next Hconfig Hstep)
      as [Hm [Hvm [He Hfinal]]]. subst final vm'.
    split; [reflexivity |]. split; [reflexivity |]. exists objects.
    split; [|exact Hfinal]. eapply initialized_heap_evolution_refl; exact Hheap.
  - destruct (coherent_scalar_array_read_preservation ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef chunk final vm' next Hconfig Hmode Hstep)
      as [Hm [Hvm Hfinal]]. subst final vm'.
    split; [reflexivity |]. split; [reflexivity |]. exists objects.
    split; [|exact Hfinal]. eapply initialized_heap_evolution_refl; exact Hheap.
  - destruct (coherent_aggregate_array_read_preservation ge Gamma Sigma vm m objects cells packets p b base elem len attr n ef final vm' next Hconfig Haggregate Hstep)
      as [Hm [Hvm [Hevolve Hfinal]]].
    split; [exact Hm |]. split; [exact Hvm |]. eexists; split; eassumption.
  - subst elem.
    destruct (coherent_bytes_array_read_preservation ge Gamma Sigma vm m objects cells packets p b base len attr n ef final vm' next Hconfig Hstep)
      as [Hm [Hvm Hfinal]]. subst final vm'.
    split; [reflexivity |]. split; [reflexivity |]. exists objects.
    split; [|exact Hfinal]. eapply initialized_heap_evolution_refl; exact Hheap.
Qed.

Print Assumptions coherent_general_array_read_progress.
Print Assumptions coherent_general_array_read_preservation.
