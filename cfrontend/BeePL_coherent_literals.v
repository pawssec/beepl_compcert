(* Pure source heads preserve the complete shared heap, including the address
   evidence already required for internal Addr expressions. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_runtime_locations BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_literal_consistency.
Import ListNotations.

Theorem coherent_constant_progress : forall ge Gamma Sigma vm m objects cells packets p c ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Const c ty) ef ty ->
  exists v, ssem_expr ge p vm m (Const c ty) m vm (Val v ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val v ty) ef ty.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent].
  destruct (typed_constant_progress ge p vm m Gamma Sigma c ty ef ty Htyped)
    as [v [Hstep [_ Hvalue]]].
  exists v. split; [exact Hstep|]. split; [eapply initialized_heap_evolution_refl; exact Hheap|].
  inversion Htyped; subst; inversion Hstep; subst.
  all: split; [|exact Hcoherent]; constructor; auto; exact I.
Qed.

Theorem coherent_constant_preservation : forall ge Gamma Sigma vm m objects cells packets p c ty ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Const c ty) ef ty ->
  ssem_expr ge p vm m (Const c ty) final vm' next ->
  final=m /\ vm'=vm /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next ef ty.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent] Hstep.
  destruct (typed_constant_preservation ge p vm m Gamma Sigma c ty ef ty final vm' next Htyped Hstep)
    as [Hm [Hvm [v [He Hvalue]]]]. subst final vm' next.
  split; [reflexivity|]. split; [reflexivity|]. split; [eapply initialized_heap_evolution_refl; exact Hheap|].
  inversion Htyped; subst; inversion Hstep; subst.
  all: split; [|exact Hcoherent]; constructor; auto; exact I.
Qed.

Theorem coherent_unit_progress : forall ge Gamma Sigma vm m objects cells packets p ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Unit ty) ef ty ->
  ssem_expr ge p vm m (Unit ty) m vm (Val Vunit ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val Vunit ty) ef ty.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent]. inversion Htyped; subst.
  split; [constructor|]. split; [eapply initialized_heap_evolution_refl; exact Hheap|].
  split; [|exact Hcoherent]; constructor; auto; constructor.
Qed.

Theorem coherent_unit_preservation : forall ge Gamma Sigma vm m objects cells packets p ty ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Unit ty) ef ty ->
  ssem_expr ge p vm m (Unit ty) final vm' next ->
  final=m /\ vm'=vm /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next ef ty.
Proof.
  intros * Hconfig Hstep. inversion Hstep; subst.
  destruct (coherent_unit_progress _ _ _ _ _ _ _ _ p _ _ Hconfig) as [_ [Hevolve Hfinal]].
  auto.
Qed.

Theorem coherent_address_progress : forall ge Gamma Sigma vm m objects cells packets p loc ofs ty ef,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Addr loc ofs ty) ef ty ->
  ssem_expr ge p vm m (Addr loc ofs ty) m vm (Val (Vloc loc.(lname) ofs) ty) /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma m objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Val (Vloc loc.(lname) ofs) ty) ef ty.
Proof.
  intros * [[Hheap Htyped Hloc Hframes] Hcoherent]. inversion Htyped; subst.
  split; [constructor|]. split; [eapply initialized_heap_evolution_refl; exact Hheap|].
  split; [|exact Hcoherent]; constructor; auto. constructor; assumption.
Qed.

Theorem coherent_address_preservation : forall ge Gamma Sigma vm m objects cells packets p loc ofs ty ef final vm' next,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets (Addr loc ofs ty) ef ty ->
  ssem_expr ge p vm m (Addr loc ofs ty) final vm' next ->
  final=m /\ vm'=vm /\
    initialized_heap_evolution ge Sigma objects cells packets Sigma final objects cells packets /\
    coherent_runtime_configuration ge Gamma Sigma vm' final objects cells packets next ef ty.
Proof.
  intros * Hconfig Hstep. inversion Hstep; subst.
  destruct (coherent_address_progress _ _ _ _ _ _ _ _ p _ _ _ _ Hconfig) as [_ [Hevolve Hfinal]].
  auto.
Qed.

Print Assumptions coherent_constant_preservation.
Print Assumptions coherent_unit_preservation.
Print Assumptions coherent_address_preservation.
