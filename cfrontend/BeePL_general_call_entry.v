(* General internal call entry: immutable code aliases plus all admitted data
   arguments, sharing the actual initialized heap with the caller. *)
Require Import List Bool Classical Coqlib Integers AST Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_substitution_proofs BeePL_soundness_memory BeePL_soundness_store BeePL_runtime_locations.
Require Import BeePL_general_call_preparation BeePL_general_callee_bindings BeePL_function_parameters.
Require Import BeePL_parameter_storage_check BeePL_storage_types BeePL_parameter_allocations.
Require Import BeePL_initialized_runtime BeePL_coherent_configurations BeePL_program_runtime.
Require Import BeePL_callable_locations BeePL_packet_bindings BeePL_packet_heap BeePL_packet_state.
Require Import BeePL_aggregate_memory BeePL_layout_coherence BeePL_code_contracts BeePL_frame_free.
Require Import BeePL_call_entry BeePL_callable_entry BeePL_application_configuration.
Import ListNotations.

Theorem general_internal_call_entry : forall p globals Gamma Sigma caller m objects cells packets b fn es,
  program_runtime_invariant(globalenv p) globals Sigma objects cells packets ->
  Genv.find_funct(globalenv p)(Values.Vptr b Ptrofs.zero)=Some(Internal fn) ->
  type_exprs p.(prog_comp_env) Gamma Sigma es [] (seq.unzip2(fn_args fn)) ->
  Forall(fun e=>exists v annotation,e=Val v annotation) es ->
  all_expr_locations(runtime_locations(packet_heap_locations(globalenv p) cells objects packets)) es ->
  initialized_heap_state(globalenv p) Gamma Sigma caller m objects cells packets ->coherent_layout cells ->
  exists callee final Sigma' objects' cells' packets',
    ssem_expr(globalenv p) p caller m
      (App(Val(Vloc b Ptrofs.zero)(type_of_function fn)) es(fn_return fn))
      final caller(CallFrame callee(fn_body fn)(fn_return fn)) /\
    initialized_heap_evolution(globalenv p) Sigma objects cells packets Sigma' final objects' cells' packets' /\
    coherent_runtime_configuration(globalenv p) Gamma Sigma' caller final objects' cells' packets'
      (CallFrame callee(fn_body fn)(fn_return fn))(fn_effect fn)(fn_return fn).
Proof.
  intros p globals Gamma Sigma caller m objects cells packets b fn es Hprogram Hfind Hargs Hvalues Hlocations Hheap Hcoherent.
  pose proof(program_runtime_code _ _ _ _ _ _ Hprogram _ _ Hfind) as Hfn.
  assert(Hnorepet:list_norepet(seq.unzip1(fn_args fn))) by(inversion Hfn;assumption).
  assert(Hnames:NoDup(map fst(fn_args fn))) by(inversion Hfn;subst;apply parameter_names_nodup;assumption).
  assert(Hstorage:parameters_storage_check p.(prog_comp_env)(fn_args fn)=true) by(inversion Hfn;assumption).
  assert(Hfacts:general_argument_values(globalenv p) Gamma Sigma
    (packet_heap_locations(globalenv p) cells objects packets)(fn_args fn)(extract_values_exprs es))
    by(eapply general_typed_located_arguments;eauto).
  destruct(general_function_parameter_partition (globalenv p) Gamma Sigma
    (packet_heap_locations(globalenv p) cells objects packets)(fn_args fn)(extract_values_exprs es) ltac:(
    intros block args effects result variadic Hloc;
    destruct Hloc as [[Hcall|[[Hkind Hobject]|[basic [attr [Hbad Hobject]]]]]|[Hbytes Hpacket]];
      [exact Hcall|discriminate Hkind|discriminate Hbad|discriminate Hbytes]) Hfacts)
    as [codes [data [data_values [Hpartition HdataValues]]]].
  assert(HdataStorage:Forall(fun param=>storage_type_check p.(prog_comp_env)(snd param)=true)data).
  { eapply parameters_storage_data_list;[exact Hstorage| |eapply function_partition_data_nonfunction;exact Hpartition].
    intros item Hin;eapply function_partition_data_in;eauto. }
  assert(HdataNames:NoDup(map fst data)) by(eapply function_partition_data_names;eauto).
  destruct(general_parameter_heap_preparation(globalenv p) p Gamma Sigma caller m objects cells packets data data_values codes
    eq_refl Hheap Hcoherent HdataStorage HdataNames HdataValues)
    as [callee [allocated [final [Sigma' [objects' [cells' [packets' [Ha [Hb [Hevol [Hcoherent' HdataBindings]]]]]]]]]]].
  pose proof(initialized_evolution_store _ _ _ _ _ _ _ _ _ _ Hevol) as Hext.
  assert(Hcallee:packet_variable_layout(bind_vars globals(fn_args fn)) Sigma'(globalenv p) callee cells' objects' packets').
  { eapply general_callee_packet_bindings;[exact Hpartition|exact Hnames|exact(program_runtime_globals _ _ _ _ _ _ Hprogram)|exact Ha|exact Hext| | | |exact HdataBindings].
    - intros;eapply initialized_evolution_cells;[exact Hevol|eassumption].
    - intros;eapply initialized_evolution_objects;[exact Hevol|eassumption].
    - intros;eapply initialized_evolution_packet_locations;[exact Hevol|eassumption]. }
  assert(Hbodytyped:type_expr p.(prog_comp_env)(bind_vars globals(fn_args fn)) Sigma'
    (fn_body fn)(fn_effect fn)(fn_return fn)).
  { inversion Hfn;subst;eapply(proj2 typing_store_extension);eauto. }
  assert(Hannotations:typeof_exprs es=seq.unzip2(fn_args fn)) by(eapply typed_arguments_annotations;eauto).
  exists callee,final,Sigma',objects',cells',packets';split.
  - destruct(classic(has_function_parameter(fn_args fn))) as [Hhas|Hnone].
    + unfold type_of_function;rewrite <-Hannotations;eapply ssem_app_code_parameters;eauto;reflexivity.
    + destruct(partition_without_functions _ _ _ _ _ _ Hpartition Hnone) as [Hcodes [Hdata Hvals]].
      subst codes data data_values. unfold type_of_function;rewrite <-Hannotations;eapply ssem_app3;eauto;reflexivity.
  - split;[exact Hevol|]. split;[|exact Hcoherent']. constructor.
    + eapply initialized_heap_state_evolve;[exact Hheap|exact Hevol].
    + eapply ty_callframe;exact Hbodytyped.
    + simpl;eapply runtime_locations_monotone;[|exact(program_runtime_bodies _ _ _ _ _ _ Hprogram _ _ Hfind)].
      eapply packet_heap_locations_monotone.
      * intros;eapply initialized_evolution_cells;[exact Hevol|eassumption].
      * intros;eapply initialized_evolution_objects;[exact Hevol|eassumption].
      * intros;eapply initialized_evolution_packet_locations;[exact Hevol|eassumption].
    + simpl;exists(bind_vars globals(fn_args fn)),(fn_effect fn);split;[exact Hcallee|]. split;[exact Hbodytyped|].
      apply frame_free_initialized_frames;exact(program_runtime_source _ _ _ _ _ _ Hprogram _ _ Hfind).
Qed.

Print Assumptions general_internal_call_entry.
