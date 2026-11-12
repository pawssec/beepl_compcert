(* State integration for the checked scalar and array cases. The remaining
   aggregate, callable, packet, and helper invariants must still be integrated. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store.
Require Import BeePL_runtime_locations BeePL_array_proofs BeePL_soundness_arrays.
Require Import BeePL_soundness_variables.
Import ListNotations.
Local Open Scope Z_scope.

Record mixed_heap_state (Gamma : ty_context) (Sigma : store_context)
    (bge : genv) (vm : vmap) (m : Mem.mem) (layout : scalar_layout) : Prop := {
  mixed_state_blocks : store_blocks_valid Sigma m;
  mixed_state_memory : typed_memory_layout bge.(genv_cenv) Sigma layout m;
  mixed_state_contents : memory_locations (array_heap_locations bge.(genv_cenv) layout) layout m;
  mixed_state_bindings : mixed_variable_layout Gamma Sigma bge vm layout
}.

Theorem mixed_array_allocation_preservation :
  forall Gamma Sigma bge vm m layout p arr pt len attr es ef m' vm' e',
  type_expr bge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  mixed_heap_state Gamma Sigma bge vm m layout ->
  runtime_locations (array_heap_locations bge.(genv_cenv) layout)
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ->
  ssem_expr bge p vm m
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) m' vm' e' ->
  exists Sigma' layout',
    store_context_extends Sigma Sigma' /\
    mixed_heap_state Gamma Sigma' bge vm' m' layout' /\
    type_expr bge.(genv_cenv) Gamma Sigma' e' ef (Atype (Vtype pt) len attr) /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout') e' /\
    (forall b ofs ty chunk, layout b ofs ty chunk -> layout' b ofs ty chunk) /\
    vm' = vm.
Proof.
  intros Gamma Sigma bge vm m layout p arr pt len attr es ef m' vm' e'
    Htyped Hvalues Hvolatile Hbound Hstate Hlocations Hstep.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  destruct (located_primitive_array_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvalues Hvolatile Hbound Hblocks Hmemory Hcontents Hlocations Hstep)
    as [Sigma' [layout' [Hext [Hblocks' [Htyped' [Hmemory' [Hcontents'
      [Hlocations' [Hinc [Hvm Hlocationinc]]]]]]]]]].
  exists Sigma', layout'. split; [exact Hext |]. split.
  - constructor; try assumption.
    subst vm'. eapply mixed_variable_layout_extend; eauto.
  - split; [exact Htyped' |]. split; [exact Hlocations' |]. split; assumption.
Qed.

Print Assumptions mixed_array_allocation_preservation.

Theorem mixed_array_allocation_progress :
  forall Gamma Sigma bge vm m layout p arr pt len attr es ef,
  type_expr bge.(genv_cenv) Gamma Sigma
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ef
    (Atype (Vtype pt) len attr) ->
  Forall (fun e => exists v t, e = Val v t) es ->
  type_is_volatile (transBeePL_type (Vtype pt)) = false ->
  sizeof_ptype pt * len <= Ptrofs.max_unsigned ->
  mixed_heap_state Gamma Sigma bge vm m layout ->
  runtime_locations (array_heap_locations bge.(genv_cenv) layout)
    (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr)) ->
  exists m' Sigma' layout' b,
    ssem_expr bge p vm m
      (Ainit arr (Atype (Vtype pt) len attr) es (Atype (Vtype pt) len attr))
      m' vm (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) /\
    store_context_extends Sigma Sigma' /\
    mixed_heap_state Gamma Sigma' bge vm m' layout' /\
    type_expr bge.(genv_cenv) Gamma Sigma'
      (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)) ef (Atype (Vtype pt) len attr) /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout')
      (Val (Vloc b Ptrofs.zero) (Atype (Vtype pt) len attr)).
Proof.
  intros Gamma Sigma bge vm m layout p arr pt len attr es ef
    Htyped Hvalues Hvolatile Hbound Hstate Hlocations.
  destruct (source_primitive_array_progress bge bge.(genv_cenv) Gamma Sigma layout
    p vm m arr pt len attr es ef Htyped Hvalues Hvolatile Hbound
    (mixed_state_blocks _ _ _ _ _ _ Hstate) (mixed_state_memory _ _ _ _ _ _ Hstate))
    as [vm' [m' [allocated [b [Hstep Hrest]]]]].
  destruct (mixed_array_allocation_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htyped Hvalues Hvolatile Hbound Hstate Hlocations Hstep)
    as [Sigma' [layout' [Hext [Hstate' [Htype' [Hloc' [Hinc Hvm]]]]]]].
  subst vm'. exists m', Sigma', layout', b. split; [exact Hstep |].
  split; [exact Hext |]. split; [exact Hstate' |]. split; assumption.
Qed.

Print Assumptions mixed_array_allocation_progress.

Theorem mixed_state_variable_progress : forall Gamma Sigma bge vm m layout p x ty ef,
  mixed_heap_state Gamma Sigma bge vm m layout ->
  type_expr bge.(genv_cenv) Gamma Sigma (Var x ty) ef ty ->
  exists v,
    ssem_expr bge p vm m (Var x ty) m vm (Val v ty) /\
    type_expr bge.(genv_cenv) Gamma Sigma (Val v ty) ef ty /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) (Val v ty).
Proof.
  intros Gamma Sigma bge vm m layout p x ty ef Hstate Htyped.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  inversion Htyped; subst. eapply mixed_variable_progress; eauto.
Qed.

Theorem mixed_state_variable_preservation :
  forall Gamma Sigma bge vm m layout p x ty ef m' vm' e',
  mixed_heap_state Gamma Sigma bge vm m layout ->
  type_expr bge.(genv_cenv) Gamma Sigma (Var x ty) ef ty ->
  ssem_expr bge p vm m (Var x ty) m' vm' e' ->
  mixed_heap_state Gamma Sigma bge vm' m' layout /\
  type_expr bge.(genv_cenv) Gamma Sigma e' ef ty /\
  runtime_locations (array_heap_locations bge.(genv_cenv) layout) e'.
Proof.
  intros Gamma Sigma bge vm m layout p x ty ef m' vm' e' Hstate Htyped Hstep.
  destruct Hstate as [Hblocks Hmemory Hcontents Hbindings].
  inversion Htyped; subst.
  assert (Hresult : m' = m /\ vm' = vm /\
    type_expr bge.(genv_cenv) Gamma Sigma e' nil ty /\
    runtime_locations (array_heap_locations bge.(genv_cenv) layout) e').
  { eapply mixed_variable_preservation; eauto. }
  destruct Hresult as [Hm [Hvm [Htype Hloc]]]. subst m' vm'.
  split; [constructor; assumption |]. split; assumption.
Qed.

Print Assumptions mixed_state_variable_progress.
Print Assumptions mixed_state_variable_preservation.

Definition empty_heap_layout : scalar_layout := fun _ _ _ _ => False.

Lemma mixed_heap_state_empty : forall bge,
  mixed_heap_state empty_context empty_stcontext bge empty_vmap Mem.empty empty_heap_layout.
Proof.
  intros. constructor.
  - intros b ty Hget. rewrite PTree.gempty in Hget. discriminate.
  - intros b ofs ty chunk Hcell. contradiction.
  - intros b ofs ty chunk Hcell. contradiction.
  - intros x ty Hget. rewrite PTree.gempty in Hget. discriminate.
Qed.

Print Assumptions mixed_heap_state_empty.
