(* Ref works with all existing aggregate runtime locations: registered
   objects, indexed positive arrays, and empty arrays copied directly. *)
Require Import List ZArith Lia Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas.
Require Import BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_aggregate_memory BeePL_object_coverage BeePL_object_separation.
Require Import BeePL_soundness_arrays BeePL_scalar_object_layout BeePL_layout_coherence.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_packet_copy BeePL_heap_extents.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_coherent_copy BeePL_callable_array_objects BeePL_empty_array_reference.
Import ListNotations.
Local Open Scope Z_scope.

Lemma positive_array_configuration_registration :
  forall ge Gamma Sigma vm m objects cells packets b base pt len attr e ef ty,
  coherent_runtime_configuration ge Gamma Sigma vm m objects cells packets e ef ty ->
  object_type_at ge.(genv_cenv) Sigma b (Ptrofs.unsigned base) (Atype (Vtype pt) len attr) ->
  array_reference_locations ge.(genv_cenv) cells b base (Atype (Vtype pt) len attr) ->
  0 < len ->
  let objects' := add_aggregate_descriptor objects b base (Atype (Vtype pt) len attr) in
  initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets /\
  coherent_runtime_configuration ge Gamma Sigma vm m objects' cells packets e ef ty.
Proof.
  intros * Hconfig Hobject Harray Hlen objects'.
  pose proof Hconfig as [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyping Hlocations Hframes] Hcoherent].
  destruct (register_positive_callable_array _ _ _ _ _ _ _ _ _ _ _
    Hmemory Hcoherent Hpackets Hextents Hobject Harray Hlen) as [Hmemory' [Hpackets' Hextents']].
  assert (Hevolution : initialized_heap_evolution ge Sigma objects cells packets Sigma m objects' cells packets).
  { constructor; auto using store_context_extends_refl. intros; left; assumption. }
  split; [exact Hevolution|]. split; [|exact Hcoherent].
  eapply initialized_runtime_configuration_evolve; [exact (proj1 Hconfig)|exact Hevolution].
Qed.

Lemma located_aggregate_reference_source_preparation :
  forall p Gamma Sigma vm m objects cells packets source base basic attr ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    ef (Ptrtype (Reftype basic attr)) ->
  is_aggregate_type (construct_type_btype basic)=true ->
  (exists objects',
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma m objects' cells packets /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects' cells packets
      (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      ef (Ptrtype (Reftype basic attr)) /\ objects' source base (construct_type_btype basic)) \/
  (exists pt array_attr, basic=Barray pt 0 array_attr).
Proof.
  intros * Hconfig Hkind.
  pose proof Hconfig as [[[Hblocks Hmemory Hbindings Hpackets Hextents] Htyping Hlocations Hframes] Hcoherent].
  assert (Htype : object_type_at p.(prog_comp_env) Sigma source (Ptrofs.unsigned base) (construct_type_btype basic)).
  { inversion Htyping; subst. eapply aggregate_value_object_provenance; [exact Hkind|eassumption]. }
  assert (Hsource : packet_heap_locations (globalenv p) cells objects packets source base (construct_type_btype basic))
    by exact (proj1 Hlocations).
  destruct Hsource as [Hsource|[Hbytes Hpacket]]; [|destruct basic; discriminate Hbytes].
  destruct Hsource as [Hcall|[[Haggregate Hobject]|[bt [pa [Heq Hobject]]]]].
  - destruct basic as [pt|sid sa|pt len sa]; simpl in Hkind; [discriminate| |].
    + destruct Hcall as [[pointer [chunk [Heq Hcell]]]|[elem [count [a [Heq Hrest]]]]]; discriminate Heq.
    + destruct Hcall as [[pointer [chunk [Heq Hcell]]]|Harray]; [discriminate Heq|].
      assert (Hlen : 0 <= len).
      { destruct Harray as [elem [count [a [Heq [Hcount Hcells]]]]]. inversion Heq; subst; assumption. }
      destruct (Z.eq_dec len 0) as [Hzero|Hpositive].
      * right; subst len; eauto.
      * left. exists (add_aggregate_descriptor objects source base (Atype (Vtype pt) len sa)).
        destruct (positive_array_configuration_registration _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Hconfig Htype Harray ltac:(lia)) as [Hevolution Hconfigured].
        split; [exact Hevolution|]. split; [exact Hconfigured|right; auto].
  - left; exists objects. split.
    + apply initialized_heap_evolution_refl with (Gamma := Gamma) (vm := vm).
      exact (initialized_config_heap _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig)).
    + split; assumption.
  - destruct basic; discriminate Heq.
Qed.

Theorem program_located_aggregate_reference_progress :
  forall p Gamma Sigma vm m objects cells packets source base basic attr ef,
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    ef (Ptrtype (Reftype basic attr)) ->
  is_aggregate_type (construct_type_btype basic)=true ->
  exists final fresh Sigma' objects' cells' packets',
    ssem_expr (globalenv p) p vm m
      (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm final objects' cells' packets'
      (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr))) nil (Ptrtype (Reftype basic attr)).
Proof.
  intros * Hconfig Hkind.
  destruct (located_aggregate_reference_source_preparation _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hkind)
    as [[prepared [Hprepare [Hconfigured Hsource]]]|[pt [a Hempty]]].
  - destruct (coherent_aggregate_reference_progress (globalenv p) Gamma Sigma p vm m prepared cells packets
      source base basic attr ef Hconfigured Hsource eq_refl)
      as [final [fresh [Hstep [Hevolution Hfinal]]]].
    exists final, fresh. do 4 eexists. split; [exact Hstep|]. split.
    + eapply initialized_heap_evolution_trans; [exact Hprepare|exact Hevolution].
    + exact Hfinal.
  - subst basic. destruct (empty_callable_array_reference_progress (globalenv p) Gamma Sigma p vm m objects
      cells packets source base pt a attr ef eq_refl Hconfig)
      as [final [fresh [Hstep [Hevolution Hfinal]]]].
    exists final, fresh. do 4 eexists. split; [exact Hstep|]. split; [exact Hevolution|exact Hfinal].
Qed.

Theorem program_located_aggregate_reference_preservation :
  forall p Gamma Sigma vm m objects cells packets source base basic attr ef final vm' e',
  coherent_runtime_configuration (globalenv p) Gamma Sigma vm m objects cells packets
    (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr)))
    ef (Ptrtype (Reftype basic attr)) ->
  is_aggregate_type (construct_type_btype basic)=true ->
  ssem_expr (globalenv p) p vm m
    (Prim Ref [Val (Vloc source base) (construct_type_btype basic)] (Ptrtype (Reftype basic attr))) final vm' e' ->
  exists fresh Sigma' objects' cells' packets',
    vm'=vm /\ e'=Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr)) /\
    initialized_heap_evolution (globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration (globalenv p) Gamma Sigma' vm' final objects' cells' packets' e' nil
      (Ptrtype (Reftype basic attr)) /\ sub_effect nil ef=true.
Proof.
  intros * Hconfig Hkind Hstep.
  destruct (located_aggregate_reference_source_preparation _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hkind)
    as [[prepared [Hprepare [Hconfigured Hsource]]]|[pt [a Hempty]]].
  - destruct (coherent_aggregate_reference_preservation (globalenv p) Gamma Sigma p vm m prepared cells packets
      source base basic attr ef final vm' e' Hconfigured Hsource eq_refl Hstep)
      as [fresh [Hvm [He [Hevolution [Hfinal Hsub]]]]].
    exists fresh. do 4 eexists. split; [exact Hvm|]. split; [exact He|]. split.
    + eapply initialized_heap_evolution_trans; [exact Hprepare|exact Hevolution].
    + split; [exact Hfinal|exact Hsub].
  - subst basic. destruct (empty_callable_array_reference_preservation (globalenv p) Gamma Sigma p vm m objects
      cells packets source base pt a attr ef final vm' e' Hconfig Hstep)
      as [fresh [Hvm [He [Hevolution Hfinal]]]].
    exists fresh. do 4 eexists. split; [exact Hvm|]. split; [exact He|]. split; [exact Hevolution|].
    split; [exact Hfinal|apply sub_effect_nil].
Qed.

Print Assumptions program_located_aggregate_reference_progress.
Print Assumptions program_located_aggregate_reference_preservation.
