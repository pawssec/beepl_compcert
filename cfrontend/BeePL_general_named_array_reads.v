(* Named array reads use exactly the same initialized element reads as value
   array reads, including aggregate, Bytes, and zero-sized unit elements. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_store BeePL_soundness_memory BeePL_soundness_arrays BeePL_callable_variables.
Require Import BeePL_packet_bindings BeePL_initialized_runtime BeePL_initialized_configurations.
Require Import BeePL_coherent_configurations BeePL_general_array_reads.
Import ListNotations.

Lemma packet_binding_location : forall ge Sigma vm cells objects packets x ty,
  packet_variable_binding ge Sigma vm cells objects packets x ty ->
  exists b, variable_location ge vm x ty b.
Proof.
  intros * Hbinding. destruct Hbinding as [Hcall|b Hl Hk Ho|b Hl Ht Hp]; eauto.
  destruct Hcall; unfold variable_location; eauto.
Qed.

Lemma value_array_step_to_named : forall ge p vm m x b elem len attr n final vm' next,
  variable_location ge vm x (Atype elem len attr) b ->
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b Ptrofs.zero) (Atype elem len attr)] elem) final vm' next ->
  ssem_expr ge p vm m (Aaccess x (Atype elem len attr) n elem) final vm' next.
Proof.
  intros * Hlocation Hstep. inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: rewrite ?Ptrofs.add_zero_l, ?Ptrofs.unsigned_zero in *.
  all: cbn [Z.add] in *.
  all: destruct Hlocation as [Hl|[Hnone Hsymbol]].
  all: eauto using ssem_array_access, ssem_array_access_global,
    ssem_array_access_aggregate, ssem_array_access_global_aggregate,
    ssem_array_access_unit, ssem_array_access_global_unit.
Qed.

Lemma named_array_step_to_value : forall ge p vm m x b elem len attr n final vm' next,
  variable_location ge vm x (Atype elem len attr) b ->
  ssem_expr ge p vm m (Aaccess x (Atype elem len attr) n elem) final vm' next ->
  ssem_expr ge p vm m
    (Prim (ArrayRead n) [Val (Vloc b Ptrofs.zero) (Atype elem len attr)] elem) final vm' next.
Proof.
  intros * Hlocation Hstep. inversion Hstep; subst.
  all: try match goal with H : Atype _ _ _ = Atype _ _ _ |- _ => inversion H; subst end.
  all: match goal with
  | H : PTree.get _ _ = Some (?other, _) |- _ =>
      assert (other = b) by (eapply variable_location_deterministic;
        [unfold variable_location; left; exact H|exact Hlocation]); subst other
  | H : Genv.find_symbol _ _ = Some ?other |- _ =>
      assert (other = b) by (eapply variable_location_deterministic;
        [unfold variable_location; right; split; eassumption|exact Hlocation]); subst other
  end.
  all: first
    [ solve [eapply ssem_array_read_value; rewrite ?Ptrofs.add_zero_l; eauto]
    | solve [pose proof (ssem_array_read_aggregate ge p vm' final b Ptrofs.zero elem len attr n) as Hread;
        rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_zero in Hread; cbn [Z.add] in Hread; eauto]
    | solve [eapply ssem_array_read_unit; eauto] ].
Qed.

Lemma named_array_value_configuration : forall ge Gamma Sigma vm m objects cells packets (p : program) x elem len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Aaccess x (Atype elem len attr) n elem) ef elem ->
  exists b, variable_location ge vm x (Atype elem len attr) b /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
      (Prim (ArrayRead n) [Val (Vloc b Ptrofs.zero) (Atype elem len attr)] elem) ef elem.
Proof.
  intros ge Gamma Sigma vm m objects cells packets p x elem len attr n ef Hconfig. destruct Hconfig as [Hinit Hcoherent].
  pose proof (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ Hinit) as Hheap.
  pose proof (initialized_config_typing _ _ _ _ _ _ _ _ _ _ _ Hinit) as Htyped.
  destruct (named_array_read_typing _ _ _ _ _ _ _ _ _ Htyped) as [Hef [Hx Hbound]]. subst ef.
  assert (Hdata : is_funtype elem = false) by (inversion Htyped; subst; assumption).
  destruct (packet_binding_location _ _ _ _ _ _ _ _
    (initialized_heap_bindings _ _ _ _ _ _ _ _ Hheap x _ Hx)) as [b Hlocation].
  assert (Hvar : initialized_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Var x (Atype elem len attr)) nil (Atype elem len attr)).
  { constructor; [exact Hheap|constructor; exact Hx|exact I|exact I]. }
  destruct (initialized_variable_configuration_progress _ _ _ _ _ _ _ _ p _ _ _ Hvar)
    as [v [Hstep Hvalue]].
  destruct (aggregate_variable_step_exact ge p vm m x (Atype elem len attr) b m vm (Val v (Atype elem len attr)) eq_refl Hlocation Hstep)
    as [_ [_ Heq]]. inversion Heq; subst v.
  destruct Hvalue as [_ Hvalue Hvalueloc Hvalueframes].
  exists b. split; [exact Hlocation|]. split; [|exact Hcoherent].
  constructor; simpl; auto. eapply ty_arrayread; eauto.
Qed.

Theorem coherent_named_array_read_progress : forall ge Gamma Sigma vm m objects cells packets p x elem len attr n ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Aaccess x (Atype elem len attr) n elem) ef elem ->
  exists value objects',
    ssem_expr ge p vm m (Aaccess x (Atype elem len attr) n elem) m vm (Val value elem) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects' cells packets (Val value elem) ef elem.
Proof.
  intros * Hconfig.
  destruct (named_array_value_configuration _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig)
    as [b [Hlocation Hvalue]].
  destruct (coherent_general_array_read_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ Hvalue)
    as [v [objects' [Hstep [Hevolution Hfinal]]]].
  exists v, objects'. split; [eapply value_array_step_to_named; eauto|]. auto.
Qed.

Theorem coherent_named_array_read_preservation : forall ge Gamma Sigma vm m objects cells packets p x elem len attr n ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets
    (Aaccess x (Atype elem len attr) n elem) ef elem ->
  ssem_expr ge p vm m (Aaccess x (Atype elem len attr) n elem) final vm' next ->
  final = m /\ vm' = vm /\ exists objects',
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects' cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects' cells packets next ef elem.
Proof.
  intros * Hconfig Hstep.
  destruct (named_array_value_configuration _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig)
    as [b [Hlocation Hvalue]].
  eapply coherent_general_array_read_preservation; [exact Hvalue|].
  eapply named_array_step_to_value; eauto.
Qed.

Print Assumptions coherent_named_array_read_progress.
Print Assumptions coherent_named_array_read_preservation.
