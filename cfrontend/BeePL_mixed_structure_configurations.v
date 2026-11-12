(* Every evaluated, typed source struct initializer has an actual successor
   preserving the shared heap. Fields may mix scalars, aggregates and Bytes. *)
Require Import List ZArith Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_runtime_locations BeePL_aggregate_memory BeePL_object_coverage.
Require Import BeePL_packet_heap BeePL_packet_bindings BeePL_packet_copy BeePL_initialized_runtime BeePL_coherent_configurations.
Require Import BeePL_structure_field_planning BeePL_mixed_structure_heap BeePL_structure_initializer_determinism.
Import ListNotations.

Lemma field_expressions_extract : forall fields,
 extract_values_exprs(map field_slot_expression fields)=map field_slot_value fields /\
 typeof_exprs(map field_slot_expression fields)=map field_slot_type fields.
Proof.
 induction fields as [|field fields [Hvalues Htypes]];[split;reflexivity|].
 split;simpl;congruence.
Qed.

Theorem evaluated_structure_configuration_progress : forall p Gamma Sigma vm m objects cells packets sid ids es result ef,
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets(Sinit sid ids es result) ef result ->
 Forall(fun e=>exists v ty,e=Val v ty) es ->
 exists final fresh Sigma' objects' after afterPackets,
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) final vm(Val(Vloc fresh Ptrofs.zero) result) /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' after afterPackets /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm final objects' after afterPackets
 (Val(Vloc fresh Ptrofs.zero) result) nil result.
Proof.
 intros * Hconfig Hvalues.
 pose proof Hconfig as [[Hheap Htyped Hlocations Hframes] Hcoherent].
 assert(Hshape:exists attr,structure_result_type sid attr result).
 { inversion Htyped;subst;eauto. }
 destruct Hshape as [attr Hshape].
 assert(Hlocated:Forall(fun e=>exists v ty,e=Val v ty /\value_locations(packet_heap_locations(globalenv p) cells objects packets) v ty) es).
 { change(all_expr_locations(runtime_locations(packet_heap_locations(globalenv p) cells objects packets)) es) in Hlocations.
 apply all_expr_locations_Forall in Hlocations. apply Forall_forall;intros e Hin.
 destruct(proj1(Forall_forall _ _) Hvalues e Hin) as [v [ty Heq]].
 exists v,ty;split;[exact Heq|]. subst e;exact(proj1(Forall_forall _ _) Hlocations _ Hin). }
 destruct(typed_structure_field_plan _ _ _ _ _ _ _ _ _ _ Htyped Hshape Hlocated)
 as [co [fields [Hco [Hnames [Hexprs Hvalid]]]]].
 assert(Hpa:exists pa,result=Stype sid attr \/ result=Ptrtype(Reftype(Bstruct sid attr)pa)).
 { destruct Hshape as [Heq|[pa Heq]];[exists noattr;left|exists pa;right];exact Heq. }
 destruct Hpa as [pa Hresult].
 assert(Hplanned:type_expr p.(prog_comp_env) Gamma Sigma(Sinit sid(map field_slot_name fields)(map field_slot_expression fields) result) ef result).
 { rewrite Hnames,Hexprs;exact Htyped. }
 destruct(initialize_mixed_structure_heap p Gamma Sigma vm m objects cells packets sid attr pa co fields result ef
 Hheap Hcoherent Hplanned Hshape Hco Hvalid)
 as [allocated [final [fresh [after [Halloc [Hinit [Hevolution Hcoherent']]]]]]].
 exists final,fresh,(PTree.set fresh(Ptrtype(Reftype(Bstruct sid attr)pa)) Sigma),
 (add_aggregate_descriptor objects fresh Ptrofs.zero(Stype sid attr)),after,
 (copied_object_packets p.(prog_comp_env) packets(Stype sid attr) fresh).
 split.
 - eapply ssem_sinit2 with(sa:=attr)(allocated:=allocated);[exact Hshape|exact Hvalues|exact Halloc|].
   rewrite <-Hnames,<-Hexprs. destruct(field_expressions_extract fields) as [Hvs Hts];rewrite Hvs,Hts;exact Hinit.
 - split;[exact Hevolution|]. split;[|exact Hcoherent'].
   pose proof(initialized_runtime_configuration_evolve _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig) Hevolution) as Hconfigured.
   destruct Hconfigured as [Hheap' Htyped' Hlocated' Hframes'].
   constructor;[exact Hheap'| | |exact I].
   + destruct Hresult as [Heq|Heq];subst result.
     * apply ty_valstruct;eapply aggregate_object_typing;
       [exact(initialized_object_descriptors _ _ _ _ _(initialized_heap_memory _ _ _ _ _ _ _ _ Hheap'))|right;auto].
     * apply ty_valloc;apply PTree.gss.
   + destruct Hresult as [Heq|Heq];subst result;simpl;left;right.
     * left;split;[reflexivity|right;auto].
     * right;exists(Bstruct sid attr),pa;split;[reflexivity|]. split;[reflexivity|right;auto].
Qed.

Theorem evaluated_structure_configuration_preservation : forall p Gamma Sigma vm m objects cells packets sid ids es result ef final vm' e',
 coherent_runtime_configuration(globalenv p) Gamma Sigma vm m objects cells packets(Sinit sid ids es result) ef result ->
 Forall(fun e=>exists v ty,e=Val v ty) es ->
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) final vm' e' ->
 exists fresh Sigma' objects' after afterPackets,
 vm'=vm /\e'=Val(Vloc fresh Ptrofs.zero) result /\
 initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' after afterPackets /\
 coherent_runtime_configuration(globalenv p) Gamma Sigma' vm' final objects' after afterPackets e' nil result.
Proof.
 intros * Hconfig Hvalues Hstep.
 destruct(evaluated_structure_configuration_progress _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hvalues)
 as [expected [fresh [Sigma' [objects' [after [afterPackets [Hconstructed [Hevolution Hfinal]]]]]]]].
 destruct(evaluated_structure_step_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hvalues Hconstructed Hstep)
 as [Hm [Hvm He]]. subst final vm' e'.
 exists fresh,Sigma',objects',after,afterPackets;split;[reflexivity|]. split;[reflexivity|]. split;assumption.
Qed.

Print Assumptions evaluated_structure_configuration_progress.
Print Assumptions evaluated_structure_configuration_preservation.
