(* Primitive source struct initialization in the shared initialized-object
   configuration, preserving all captured caller environments. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_soundness_store BeePL_runtime_locations BeePL_initialization_proofs.
Require Import BeePL_structure_proofs BeePL_initialized_structures.
Require Import BeePL_aggregate_memory BeePL_object_coverage.
Require Import BeePL_callable_variables BeePL_initialized_runtime.
Require Import BeePL_packet_heap BeePL_packet_bindings.
Import ListNotations.
Local Open Scope Z_scope.

Theorem initialized_structure_configuration_preservation :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e',
  initialized_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  ssem_expr (globalenv p) p vm m
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) final vm' e' ->
  exists Sigma' objects' cells',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    initialized_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets e' ef result.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co final vm' e'
    [[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes]
    Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct Hstep.
  destruct (initialized_structure_preservation Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co
    final vm' e' Hresult Htyped Hmemory Hblocks Hpackets Hextents Hco Hstruct Halign Hplain Hattrs Hdistinct
    ltac:(eapply typed_planned_structure_locations; exact Htyped) Hstep)
    as [Sigma' [objects' [cells' [Hvm [Hext [Hblocks' [Hmemory' [Htyped' [Hlocations' [Hcells [Hobjects [Hpackets' Hextents']]]]]]]]]]]].
  exists Sigma', objects', cells'. split; [constructor; auto |]. constructor.
  - constructor; try assumption. subst vm'. eapply packet_variable_layout_extend; eauto.
  - exact Htyped'.
  - eapply runtime_locations_monotone; [apply packet_descriptor_embedding|exact Hlocations'].
  - destruct (structure_initializer_step_shape _ _ _ _ _ _ _ _ _ _ _
      (planned_expressions_values fs) Hstep) as [[Hm [Hvm0 He]] | [actual_attr [allocated [fresh
        [Hshape [Halloc [Hinit [Hvm0 He]]]]]]]].
    + subst e'. eapply initialized_runtime_frames_evolve; eauto.
    + subst e'. exact I.
Qed.

Theorem initialized_structure_configuration_progress :
  forall Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co,
  initialized_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result ->
  (result = Stype sid attr \/ result = Ptrtype (Reftype (Bstruct sid attr) pa)) ->
  PTree.get sid p.(prog_comp_env) = Some co -> co.(co_su) = Struct ->
  Archi.align_int64 = 8 -> plain_members (bmembers_cmembers co.(co_members)) ->
  (forall f, In f fs -> attr_alignas (Ctypes.attr_of_type (transBeePL_type (Vtype (planned_type f)))) = None) ->
  NoDup (map planned_field fs) ->
  exists final fresh Sigma' objects' cells',
    ssem_expr (globalenv p) p vm m
      (Sinit sid (map planned_field fs) (planned_expressions fs) result) final vm
      (Val (Vloc fresh Ptrofs.zero) result) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets /\
    initialized_runtime_configuration (globalenv p) Gamma Sigma' vm final objects' cells' packets
      (Val (Vloc fresh Ptrofs.zero) result) ef result.
Proof.
  intros Gamma Sigma objects cells packets p vm m sid attr pa result fs ef co Hconfig
    Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct.
  destruct Hconfig as [[Hblocks Hmemory Hbindings Hpackets Hextents] Htyped Hlocations Hframes].
  destruct (initialized_structure_progress Gamma Sigma objects cells p vm m sid attr pa result fs ef co
    Hresult Htyped Hmemory Hblocks Hco Hstruct Halign Hplain Hattrs Hdistinct)
    as [resolved [allocated [final [fresh [allocatedStore [Hresolve [Hnames [Hexprs [Halloc [Hstep Hrest]]]]]]]]]].
  assert (Hconfig : initialized_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Sinit sid (map planned_field fs) (planned_expressions fs) result) ef result).
  { constructor; [constructor; assumption |assumption |assumption |assumption]. }
  destruct (initialized_structure_configuration_preservation Gamma Sigma objects cells packets p vm m sid attr pa result
    fs ef co final vm _ Hconfig Hresult Hco Hstruct Halign Hplain Hattrs Hdistinct Hstep)
    as [Sigma' [objects' [cells' [Hevolution Hfinal]]]].
  exists final, fresh, Sigma', objects', cells'. split; [exact Hstep |]. split; assumption.
Qed.

Print Assumptions initialized_structure_configuration_preservation.
Print Assumptions initialized_structure_configuration_progress.
