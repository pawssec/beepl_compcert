#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU Lesser General Public License as        #
#  published by the Free Software Foundation, either version 2.1 of   #
#  the License, or (at your option) any later version.                #
#  This file is also distributed under the terms of the               #
#  INRIA Non-Commercial License Agreement.                            #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib beepl common $(ARCHDIRS) backend cfrontend driver export cparser

ifeq ($(CLIGHTGEN),true)
DIRS += export
endif

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) compcert.$(d))

#DIRS += compiler_test/beepl
DIRS += compiler_test/beepl/ast compiler_test/beepl/beepl_success_load
#COQINCLUDES += -R compiler_test/beepl BeePL_Progs
COQINCLUDES += -R compiler_test/beepl/ast BeePL_Progs -R compiler_test/beepl/beepl_success_load BeePL_Progs.beepl_success_load

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

# Notes on silenced Coq warnings:
#
# unused-pattern-matching-variable:
#    warning introduced in 8.13
#    the code rewrite that avoids the warning is not desirable
# undeclared-scope:
#    warning introduced in 8.12, addressed in the main CompCert files
#    triggered by MenhirLib, to be solved upstream
# deprecated-instance-without-locality:
#    warning introduced in 8.14
#    triggered by Menhir-generated files, to be solved upstream in Menhir
# deprecated-since-8.19
# deprecated-since-8.20
#    renamings performed in Coq's standard library;
#    using the new names would break compatibility with earlier Coq versions.
# deprecated-from-Coq
#    Rocq wants "From Stdlib Require" while Coq wants "From Coq Require".

COQCOPTS ?= \
  -w -unused-pattern-matching-variable \
  -w -deprecated-ident-entry \
  -w -notation-overridden \
  -w -deprecated-since-8.19 \
  -w -deprecated-since-8.20 \
  -w -deprecated-from-Coq

cparser/Parser.vo: COQCOPTS += -w -deprecated-instance-without-locality
MenhirLib/Interpreter.vo: COQCOPTS += -w -undeclared-scope

# Flocq and Menhirlib run into other renaming issues.
# These warnings can only be addressed upstream.

flocq/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition -w -deprecated-since-9.0
MenhirLib/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition -w -deprecated-since-9.0

# For the extraction phase, we silence other warnings:
# change-dir-deprecated:
#    warning introduced in 8.20, no alternative before 8.20
# extraction-default-directory:
#    warning introduced in 8.20, no alternative before 8.20
# deprecated-from-Coq:
#    see above
COQEXTRACTOPTS ?= \
  -w -change-dir-deprecated \
  -w -extraction-default-directory \
  -w -deprecated-from-Coq

ifneq ($(INSTALL_COQDEV),true)
# Disable costly generation of .cmx files, which are not used locally
  COQCOPTS += -w -deprecated-native-compiler-option -native-compiler no
endif

ifneq (,$(TIMING))
  # does this coq version support -time-file ? (Coq >= 8.18)
  ifeq (,$(shell "$(COQBIN)coqc" -time-file /dev/null 2>&1))
    COQCOPTS += -time-file $<.timing
  endif
endif

ifneq (,$(PROFILING))
  # does this coq version dupport -profile ? (Coq >= 8.19)
  ifeq (,$(shell "$(COQBIN)coqc" -profile /dev/null 2>&1))
    COQCOPTS += -profile $<.prof.json
    PROFILE_ZIP = gzip -f $<.prof.json
  else
  endif
endif
PROFILE_ZIP ?= true

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) $(COQEXTRACTOPTS) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Plus.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  BinarySingleNaN.v Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Zbits.v Integers.v  Archi.v IEEE754_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v

# Until BeePL has a functioning lexer and parser the test programs must be
# compiled with the rest of CompCert

#BEEPL_TESTS=\
#    BeePL_progs.v \
#    BeePL_progs.v BeePL_add.v BeePL_add_ptr.v BeePL_div_zero1.v BeePL_div_zero.v \
#    BeePL_add_ex1.v BeePL_cond.v BeePL_app.v BeePL_funptr_ex1.v BeePL_bpf_get_prandom.v \
#    BeePL_for_ex1.v BeePL_for_ex2.v BeePL_match_fail_ex1.v BeePL_external_call.v BeePL_null_ptr.v \
#    BeePL_bitstring1.v BeePL_globvar1.v BeePL_bpf_xdp_packet_count.v BeePL_bpf_xdp_packet_count1.v \
#    BeePL_bpf_map_example1.v BeePL_bpf_drop_xdp_packet_iPv6.v BeePL_bpf_handle_tp.v BeePL_add_ref.v \
#    BeePL_cast.v BeePL_cast1.v BeePL_shift.v BeePL_bpf_map_null_check.v BeePL_section.v BeePL_bpf_safe_null_check.v \
#    BeePL_globvar_local.v BeePL_no_addr_return.v BeePL_check_sec.v beepl_success_load/BeePL_bpf_xdp1.v beepl_success_load/BeePL_bpf_xdp2.v \
#    beepl_success_load/BeePL_bpf_pid_tgid.v BeePL_var.v BeePL_bytes1.v BeePL_for3.v BeePL_array.v BeePL_array1.v BeePL_array2.v \
#    BeePL_some.v BeePL_some_match.v

BEEPL_TESTS=\
    BeePL_progs.v \
    BeePL_progs.v BeePL_add.v BeePL_add_ptr.v BeePL_div_zero1.v BeePL_div_zero.v \
    BeePL_add_ex1.v BeePL_cond.v BeePL_app.v BeePL_funptr_ex1.v BeePL_bpf_get_prandom.v \
    BeePL_for_ex1.v BeePL_for_ex2.v BeePL_match_fail_ex1.v BeePL_external_call.v BeePL_null_ptr.v \
    BeePL_bitstring1.v BeePL_globvar1.v BeePL_bpf_xdp_packet_count.v BeePL_bpf_xdp_packet_count1.v \
    BeePL_bpf_map_example1.v BeePL_bpf_drop_xdp_packet_iPv6.v BeePL_bpf_handle_tp.v BeePL_add_ref.v \
    BeePL_cast.v BeePL_cast1.v BeePL_shift.v BeePL_bpf_map_null_check.v BeePL_section.v BeePL_bpf_safe_null_check.v \
    BeePL_globvar_local.v BeePL_no_addr_return.v BeePL_check_sec.v BeePL_bpf_xdp1.v BeePL_bpf_xdp2.v \
    BeePL_bpf_pid_tgid.v BeePL_var.v BeePL_bytes1.v BeePL_for3.v BeePL_array.v BeePL_array1.v BeePL_array2.v \
    BeePL_some.v BeePL_some_match.v

#  BeePL_div_zero.v BeePL_div_zero1.v BeePL_external_call.v BeePL_ref.v \
#  BeePL_struct_ex2.v BeePL_for_ex1.v BeePL_for_ex2.v BeePL_globvar1.v \
#  BeePL_bpf_get_prandom.v BeePL_bpf_ktime_get_ns.v

# Parts common to BeePL

BEEPL=\
      $(BEEPL_TESTS) BeeTypes.v BeePL_values.v BeePL_bpf.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Separation.v Builtins0.v Builtins1.v Builtins.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Cminortyping.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SplitLong.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SplitLongproof.v \
  SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Unusedglob.v Unusedglobproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Debugvar.v Debugvarproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v

# C front-end modules (in cfrontend/)

CFRONTEND=BeePL_mem.v BeePL_aux.v BeePL.v BeePL_packet.v BeePL_packet_proofs.v BeePL_notations.v \
  BeePL_auxlemmas.v BeePL_helper_functions.v BeePL_sem.v \
  BeePL_typechecker.v BeePL_typesystem.v Type_proof_C.v \
  BeePL_safety.v BeePL_memory_proofs.v BeePL_operators_proofs.v BeePL_typesystem_proofs.v BeePL_proof_audit.v BeePL_soundness_memory.v BeePL_soundness_operators.v BeePL_substitution_freevars.v BeePL_substitution_proofs.v BeePL_soundness_store.v BeePL_runtime_locations.v BeePL_soundness_fields.v BeePL_allocation_proofs.v BeePL_initialization_proofs.v BeePL_layout_proofs.v BeePL_structure_proofs.v BeePL_array_proofs.v BeePL_soundness_arrays.v BeePL_soundness_variables.v BeePL_soundness_state.v BeePL_call_bindings.v BeePL_parameter_allocations.v BeePL_call_memory.v BeePL_call_state.v BeePL_call_entry.v BeePL_function_variables.v BeePL_callable_locations.v BeePL_callable_variables.v BeePL_callable_state.v BeePL_callable_entry.v BeePL_environment_preservation.v BeePL_runtime_frames.v BeePL_context_retyping.v BeePL_frame_free.v BeePL_frame_configurations.v BeePL_runtime_substitution.v BeePL_runtime_call_entry.v BeePL_type_equality.v BeePL_call_determinism.v BeePL_application_configuration.v BeePL_application_preservation.v BeePL_frame_regressions.v BeePL_scalar_parameters.v BeePL_scalar_parameter_allocations.v BeePL_scalar_arguments.v BeePL_code_contracts.v BeePL_scalar_parameter_bindings.v BeePL_scalar_call_layout.v BeePL_scalar_call_preparation.v BeePL_scalar_runtime_entry.v BeePL_scalar_call_determinism.v BeePL_scalar_application_preservation.v BeePL_option_representation.v BeePL_scalar_reference_regressions.v BeePL_option_checker_regressions.v BeePL_call_parameters.v BeePL_unit_regressions.v BeePL_value_parameter_bindings.v BeePL_call_parameter_layout.v BeePL_parameter_call_preparation.v BeePL_parameter_runtime_entry.v BeePL_parameter_application_preservation.v BeePL_aggregate_memory.v BeePL_aggregate_dereference.v BeePL_interior_array_regressions.v BeePL_copy_bytes.v BeePL_copy_cells.v BeePL_copy_regressions.v BeePL_aggregate_copy.v BeePL_aggregate_copy_regressions.v BeePL_array_copy_layout.v BeePL_structure_copy_layout.v BeePL_fresh_copy.v BeePL_fresh_aggregate_memory.v BeePL_aggregate_reference.v BeePL_aggregate_reference_regressions.v BeePL_object_paths.v BeePL_scalar_object_layout.v BeePL_object_separation.v BeePL_object_coverage.v BeePL_covered_reads.v BeePL_initialized_reference.v BeePL_object_coverage_regressions.v BeePL_aggregate_array_elements.v BeePL_aggregate_array_reads.v BeePL_nested_array_execution.v BeePL_initializer_frames.v BeePL_array_object_coverage.v BeePL_initialized_arrays.v BeePL_initialized_parameters.v BeePL_initialized_array_execution.v BeePL_initialized_structures.v BeePL_initialized_call_entry.v BeePL_initialized_variables.v BeePL_block_extents.v BeePL_heap_extents.v BeePL_callable_array_objects.v BeePL_callable_scalar_arrays.v BeePL_extent_copy_readiness.v BeePL_packet_schema_check.v BeePL_packet_schema_audit.v BeePL_packet_header_extents.v BeePL_packet_header_layout.v BeePL_initialized_packet_header.v BeePL_parameter_extents.v BeePL_initialized_runtime.v BeePL_program_runtime.v BeePL_initialized_application_entry.v BeePL_initialized_configurations.v BeePL_initialized_structure_configurations.v BeePL_initialized_application_preservation.v BeePL_initialized_substitution.v BeePL_initialized_lists.v BeePL_initialized_contexts.v BeePL_initialized_control.v BeePL_initialized_mutation.v BeePL_layout_coherence.v BeePL_coherent_configurations.v BeePL_coherent_copy.v BeePL_coherent_parameters.v BeePL_coherent_call_entry.v BeePL_coherent_application_entry.v BeePL_coherent_application_preservation.v BeePL_coherent_structures.v BeePL_coherent_references.v BeePL_coherent_reference_execution.v BeePL_unit_arrays.v BeePL_program_member_types.v BeePL_initialized_unit_arrays.v BeePL_coherent_reads.v BeePL_initialized_aggregate_mutation.v BeePL_coherent_operators.v BeePL_coherent_loops.v BeePL_structure_mutation_footprint.v BeePL_loop_execution.v BeePL_checker_consistency.v BeePL_strict_progress.v BeePL_function_parameters.v BeePL_function_parameter_storage.v BeePL_function_parameter_bindings.v BeePL_function_parameter_entry.v BeePL_function_parameter_determinism.v BeePL_function_parameter_regressions.v BeePL_literal_consistency.v BeePL_cast_soundness.v BeePL_branch_cast_checker.v BeePL_coherent_casts.v BeePL_coherent_control.v BeePL_bool_cast_compiler.v BeePL_cast_evaluation.v BeePL_volatile_audit.v BeePL_object_finiteness.v BeePL_finite_reachability.v BeePL_memory_checker.v BeePL_object_edges.v BeePL_function_array_audit.v BeePL_worklist_reachability.v BeePL_object_decision.v BeePL_value_checker.v BeePL_packet_descriptor_copy.v BeePL_storage_types.v BeePL_array_storage_typing.v BeePL_structure_storage_typing.v BeePL_packet_state.v BeePL_bytes_layout.v BeePL_bytes_execution.v BeePL_structure_variables.v BeePL_packet_heap.v BeePL_packet_bindings.v BeePL_packet_copy.v BeePL_packet_replacement.v BeePL_packet_object_layout.v BeePL_packet_object_coherence.v BeePL_packet_location_coherence.v BeePL_packet_alignment.v BeePL_scalar_object_coherence.v BeePL_initializer_slot.v BeePL_general_array_initialization.v BeePL_copy_array_initialization.v BeePL_structure_initializer_slots.v BeePL_scalar_structure_coverage.v BeePL_parameter_storage_check.v BeePL_storage_parameter_allocations.v BeePL_call_storage_audit.v BeePL_function_array_state_audit.v BeePL_initializer_determinism.v BeePL_array_copy_sources.v BeePL_array_packet_assembly.v BeePL_copy_array_heap.v BeePL_scalar_array_heap.v BeePL_general_array_configurations.v BeePL_general_array_reads.v BeePL_general_named_array_reads.v BeePL_coherent_aggregate_dereference.v BeePL_coherent_lists.v BeePL_coherent_array_contexts.v BeePL_coherent_memory_contexts.v BeePL_general_reference_heads.v BeePL_reference_induction.v BeePL_general_memory_heads.v BeePL_aggregate_parameter_heap.v BeePL_scalar_parameter_heap.v BeePL_bytes_parameter_heap.v BeePL_structure_copy_regions.v BeePL_declared_copy_field.v BeePL_coherent_literals.v BeePL_loop_freevars_audit.v BeePL_typed_substitution_freevars.v BeePL_match_arity.v BeePL_packet_match_freevars.v BeePL_step_freevars.v BeePL_coherent_loop_contexts.v BeePL_mixed_structure_fields.v BeePL_mixed_structure_coverage.v BeePL_mixed_structure_heap.v BeePL_mixed_structure_configurations.v BeePL_coherent_scope_cases.v BeePL_coherent_option_cases.v BeePL_parameter_slot_heap.v BeePL_memory_induction.v BeePL_field_induction.v BeePL_coherent_match_cases.v BeePL_coherent_array_cases.v BeePL_coherent_for_cases.v BeePL_parameter_heap_fold.v BeePL_general_call_preparation.v BeePL_general_callee_bindings.v BeePL_general_call_entry.v BeePL_general_call_determinism.v BeePL_general_application.v BeePL_legacy_soundness_audit.v BeePL_program_induction.v BeePL_program_control_cases.v BeePL_program_leaf_cases.v BeePL_program_composite_cases.v BeePL_program_primitive_case.v BeePL_program_structure_case.v BeePL_program_application_case.v BeePL_program_soundness_assembly.v BeePL_program_multistep.v BeePL_initial_program.v BeePL_initial_program_execution.v BeePL_nested_option_model.v BeePL_nested_option_tags.v BeePL_nested_option_elaboration.v BeePL_parameter_packet_assembly.v BeePL_structure_initializer_determinism.v BeePL_scalar_structure_preservation.v BeePL_structure_copy_slots.v BeePL_compatible_copy_slot.v BeePL_copy_parameter_binding.v BeePL_general_parameter_binding.v BeePL_structure_field_planning.v BeePL_scalar_structure_heap.v BeePL_empty_array_reference.v BeePL_located_aggregate_reference.v BeePL_copy_array_coverage.v BeePL_copy_array_views.v BeePL_initializer_coherence.v BeePL_scalar_location_coherence.v BeePL_coherent_fields.v BeePL_packet_mutation.v BeePL_packet_coverage.v BeePL_bytes_fields.v BeePL_nested_unit_array_copy.v BeePL_structure_source_regressions.v BeePL_structure_object_coverage.v BeePL_call_frames.v BeePL_function_scope_proofs.v BeePL_loop_proofs.v \
  BeePL_alpha_renaming.v BeePL_Check_Reserved_Struct.v BeePL_Bytes_Struct.v BeePL_Wrapper_Pass.v BeePL_escape_types.v BeePL_escape_helpers.v BeePL_escape_check.v BeePL_escape_policy.v BeePL_escape_resolution.v BeePL_Csyntax.v \
  BeePL_compiler_scoped_values.v BeePL_compiler_loop_rvalue_audit.v BeePL_compiler_binding_evaluation.v BeePL_compiler_bindings.v BeePL_compiler_reference_child.v BeePL_compiler_reference_step.v BeePL_compiler_source_semantics_audit.v BeePL_compiler_aggregate_confinement.v BeePL_compiler_temporary_frame.v BeePL_compiler_tail_calls.v BeePL_compiler_representation.v BeePL_compiler_array_rhs.v BeePL_binary_capture_evaluation.v BeePL_compiler_dereference_translation.v BeePL_representation_check.v BeePL_raw_ibool_audit.v BeePL_compiler_rvalue_audit.v BeePL_compiler_variable_read.v BeePL_compiler_bool_read.v BeePL_compiler_dereference_evaluation.v BeePL_compiler_cast_evaluation.v BeePL_compiler_binary_translation.v BeePL_compiler_statement_decomposition.v BeePL_compiler_frame_release.v BeePL_escape_store.v BeePL_compiler_frame_confinement.v BeePL_compiler_reference_evaluation.v BeePL_compiler_escape.v BeePL_compiler_lifetime_audit.v BeePL_compiler_reserved_names.v BeePL_compiler_memory_injection.v BeePL_compiler_parameter_audit.v BeePL_compiler_statement_growth.v BeePL_compiler_initial_memory.v BeePL_compiler_composites.v BeePL_compiler_context_growth.v BeePL_compiler_operator_translation.v BeePL_compiler_decomposition.v BeePL_compiler_local_allocation.v BeePL_option_capture_evaluation.v BeePL_compiler_globals.v BeePL_compiler_context_audit.v BeePL_compiler_structure.v BeePL_compiler_expression_types.v BeePL_compiler_proofs.v Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  BeePL_Csyntax.v Cshmgen.v Cshmgenproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# Parser

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# Putting everything together (in driver/)
DRIVER=Compopts.v Compiler.v Complements.v

# Library for .v files generated by clightgen

ifeq ($(CLIGHTGEN),true)
EXPORTLIB=Ctypesdefs.v Clightdefs.v Csyntaxdefs.v
else
# Include EXPORTLIB files in ccomp for BeePL compiler
EXPORTLIB=Ctypesdefs.v Clightdefs.v Csyntaxdefs.v
endif

# All source files

FILES=$(VLIB) $(BEEPL) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(PARSER) $(EXPORTLIB)

# Include eBPF-specific dependencies in coqdep's input, so a clean parallel
# build schedules them after the libraries they import.
ifeq ($(ARCH),ebpf)
FILES += Size.v Mulh.v Asmgen_shift_tests.v
endif

# Generated source files

GENERATED=\
  $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v $(ARCH)/SelectLong.v \
  backend/SelectDiv.v backend/SplitLong.v \
  cparser/Parser.v

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif
ifeq ($(INSTALL_COQDEV),true)
	$(MAKE) compcert.config
endif

proof: $(FILES:.v=.vo)

# Re-run the dependency audit even when all proof objects are up to date.
soundness-check: cfrontend/BeePL_typesystem_proofs.vo cfrontend/BeePL_initial_program_execution.vo
	@mkdir -p evaluation/results
	@echo "Auditing BeePL source soundness assumptions"
	@$(COQEXEC) cfrontend/BeePL_soundness_assumptions.v > evaluation/results/type-soundness-assumptions.log
	@sh evaluation/tools/check_proof_assumptions.sh evaluation/results/type-soundness-assumptions.log

soundness-kernel-check: soundness-check
	@$(COQCHK) -silent compcert.cfrontend.BeePL_typesystem_proofs compcert.cfrontend.BeePL_initial_program_execution

# Checked compiler foundations only; unfinished whole-program simulation is excluded.
compiler-check: cfrontend/BeePL_compiler_scoped_values.vo cfrontend/BeePL_compiler_loop_rvalue_audit.vo cfrontend/BeePL_compiler_binding_evaluation.vo cfrontend/BeePL_compiler_bindings.vo cfrontend/BeePL_compiler_reference_child.vo cfrontend/BeePL_compiler_reference_step.vo cfrontend/BeePL_compiler_source_semantics_audit.vo cfrontend/BeePL_compiler_aggregate_confinement.vo cfrontend/BeePL_compiler_temporary_frame.vo cfrontend/BeePL_compiler_tail_calls.vo cfrontend/BeePL_compiler_representation.vo cfrontend/BeePL_compiler_array_rhs.vo cfrontend/BeePL_binary_capture_evaluation.vo cfrontend/BeePL_compiler_dereference_translation.vo cfrontend/BeePL_representation_check.vo cfrontend/BeePL_raw_ibool_audit.vo cfrontend/BeePL_compiler_rvalue_audit.vo cfrontend/BeePL_compiler_variable_read.vo cfrontend/BeePL_compiler_bool_read.vo cfrontend/BeePL_compiler_dereference_evaluation.vo cfrontend/BeePL_compiler_cast_evaluation.vo cfrontend/BeePL_compiler_binary_translation.vo cfrontend/BeePL_compiler_statement_decomposition.vo cfrontend/BeePL_compiler_frame_release.vo cfrontend/BeePL_escape_store.vo cfrontend/BeePL_compiler_frame_confinement.vo cfrontend/BeePL_compiler_reference_evaluation.vo cfrontend/BeePL_escape_resolution.vo cfrontend/BeePL_escape_policy.vo cfrontend/BeePL_compiler_escape.vo cfrontend/BeePL_compiler_lifetime_audit.vo cfrontend/BeePL_compiler_reserved_names.vo cfrontend/BeePL_compiler_memory_injection.vo cfrontend/BeePL_compiler_parameter_audit.vo cfrontend/BeePL_compiler_statement_growth.vo cfrontend/BeePL_compiler_initial_memory.vo cfrontend/BeePL_compiler_composites.vo cfrontend/BeePL_compiler_context_growth.vo cfrontend/BeePL_compiler_operator_translation.vo cfrontend/BeePL_compiler_decomposition.vo cfrontend/BeePL_compiler_local_allocation.vo cfrontend/BeePL_option_capture_evaluation.vo cfrontend/BeePL_compiler_expression_types.vo cfrontend/BeePL_compiler_structure.vo cfrontend/BeePL_compiler_globals.vo cfrontend/BeePL_compiler_context_audit.vo
	@mkdir -p evaluation/results
	@echo "Auditing checked compiler foundations (not full semantic preservation)"
	@$(COQEXEC) cfrontend/BeePL_compiler_assumptions.v > evaluation/results/compiler-assumptions.log
	@sh evaluation/tools/check_proof_assumptions.sh --compiler evaluation/results/compiler-assumptions.log

compiler-kernel-check: compiler-check
	@$(COQCHK) -silent compcert.cfrontend.BeePL_compiler_scoped_values compcert.cfrontend.BeePL_compiler_loop_rvalue_audit compcert.cfrontend.BeePL_compiler_binding_evaluation compcert.cfrontend.BeePL_compiler_bindings compcert.cfrontend.BeePL_compiler_reference_child compcert.cfrontend.BeePL_compiler_reference_step compcert.cfrontend.BeePL_compiler_source_semantics_audit compcert.cfrontend.BeePL_compiler_aggregate_confinement compcert.cfrontend.BeePL_compiler_temporary_frame compcert.cfrontend.BeePL_compiler_tail_calls compcert.cfrontend.BeePL_compiler_representation compcert.cfrontend.BeePL_compiler_array_rhs compcert.cfrontend.BeePL_binary_capture_evaluation compcert.cfrontend.BeePL_compiler_dereference_translation compcert.cfrontend.BeePL_representation_check compcert.cfrontend.BeePL_raw_ibool_audit compcert.cfrontend.BeePL_compiler_rvalue_audit compcert.cfrontend.BeePL_compiler_variable_read compcert.cfrontend.BeePL_compiler_bool_read compcert.cfrontend.BeePL_compiler_dereference_evaluation compcert.cfrontend.BeePL_compiler_cast_evaluation compcert.cfrontend.BeePL_compiler_binary_translation compcert.cfrontend.BeePL_compiler_statement_decomposition compcert.cfrontend.BeePL_compiler_frame_release compcert.cfrontend.BeePL_escape_store compcert.cfrontend.BeePL_compiler_frame_confinement compcert.cfrontend.BeePL_compiler_reference_evaluation compcert.cfrontend.BeePL_escape_resolution compcert.cfrontend.BeePL_escape_policy compcert.cfrontend.BeePL_compiler_escape compcert.cfrontend.BeePL_compiler_expression_types compcert.cfrontend.BeePL_compiler_structure compcert.cfrontend.BeePL_compiler_globals compcert.cfrontend.BeePL_compiler_context_audit compcert.cfrontend.BeePL_compiler_decomposition compcert.cfrontend.BeePL_compiler_local_allocation compcert.cfrontend.BeePL_option_capture_evaluation compcert.cfrontend.BeePL_compiler_operator_translation compcert.cfrontend.BeePL_compiler_initial_memory compcert.cfrontend.BeePL_compiler_composites compcert.cfrontend.BeePL_compiler_context_growth compcert.cfrontend.BeePL_compiler_statement_growth compcert.cfrontend.BeePL_compiler_memory_injection compcert.cfrontend.BeePL_compiler_parameter_audit compcert.cfrontend.BeePL_compiler_reserved_names compcert.cfrontend.BeePL_compiler_lifetime_audit

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	@if grep 'AXIOM TO BE REALIZED' extraction/*.ml; then \
            echo "An error occured during extraction to OCaml code."; \
            echo "Check the versions of Flocq and MenhirLib used."; \
            exit 2; \
         fi
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof soundness-check soundness-kernel-check compiler-check compiler-kernel-check extraction runtime FORCE

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	coq2html -d doc/html/ -base compcert -short-names \
	  $(patsubst %, %/*.glob, $(DIRS)) \
          $(filter-out cparser/Parser.v, $^)

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun -I +str str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun -I +str str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder -I +str str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder -I +str str.cma tools/modorder.ml
endif

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) $*.v
	@$(PROFILE_ZIP)

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(RELLIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_linking_step=$(HAS_LINKING_STEP)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

compcert.config: Makefile.config
	(echo "# CompCert configuration parameters"; \
        echo "COMPCERT_ARCH=$(ARCH)"; \
        echo "COMPCERT_MODEL=$(MODEL)"; \
        echo "COMPCERT_ABI=$(ABI)"; \
        echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
        echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
        echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
        echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
        echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
        echo "COMPCERT_TAG=$(TAG)"; \
        echo "COMPCERT_BRANCH=$(BRANCH)" \
        ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	@rm -f $@
	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
	@chmod a-w $@

depend: $(GENERATED) .depend

depend1: .depend

# Refresh imported-module dependencies when Coq sources or the module list
# change, including for direct .vo targets and parallel builds.
.depend: $(FILES) Makefile
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $(filter %.v,$^) > $@.tmp && mv $@.tmp $@

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./ccomp $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./compcert.ini $(DESTDIR)$(SHAREDIR)
	install -d $(DESTDIR)$(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(DESTDIR)$(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(DESTDIR)$(BINDIR)
endif
ifeq ($(INSTALL_COQDEV),true)
	install -d $(DESTDIR)$(COQDEVDIR)
	for d in $(DIRS); do \
          set -e; \
          install -d $(DESTDIR)$(COQDEVDIR)/$$d; \
          install -m 0644 $$d/*.v $$d/*.vo $$d/*.glob $(DESTDIR)$(COQDEVDIR)/$$d/; \
          if test -d $$d/.coq-native; then \
            install -d $(DESTDIR)$(COQDEVDIR)/$$d/.coq-native; \
            install -m 0644 $$d/.coq-native/* $(DESTDIR)$(COQDEVDIR)/$$d/.coq-native/; \
          fi \
	done
	install -m 0644 ./VERSION $(DESTDIR)$(COQDEVDIR)
	install -m 0644 ./compcert.config $(DESTDIR)$(COQDEVDIR)
	@(echo "To use, pass the following to coq_makefile or add the following to _CoqProject:"; echo "-R $(COQDEVDIR) compcert") > $(DESTDIR)$(COQDEVDIR)/README
endif


clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf $(patsubst %, %/.coq-native, $(DIRS))
	rm -f $(patsubst %, %/*.glob, $(DIRS))
	rm -rf doc/html
	rm -f driver/Version.ml
	rm -f compcert.ini compcert.config
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	rm -f test.log test_dummy
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@if grep -w 'admit\|Admitted\|ADMITTED' $^; \
         then exit 2; else echo "Nothing admitted."; fi

check-leftovers: $(FILES)
	@if grep -w '^Check\|^Print\|^Search' $^; \
         then exit 2; else echo "No leftover interactive commands."; fi

check-proof: $(FILES)
	$(COQCHK) compcert.driver.Complements

print-includes:
	@echo $(COQINCLUDES)

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

beepl-compile-test: ccomp
	@set -u; \
	: "$${TEST_DIR:?Usage: make beepl-compile-test TEST_DIR=path/to/tests}"; \
	DIR="$$TEST_DIR"; \
	LOG=test.log; \
	> "$$LOG"; \
	if date --iso-8601=seconds >/dev/null 2>&1; then \
		NOW=$$(date --iso-8601=seconds); \
	else \
		NOW=$$(date); \
	fi; \
	printf "Compile run: %s\nDirectory: %s\n\n" "$$NOW" "$$DIR" >> "$$LOG"; \
	total=0; succ=0; fail=0; \
	for f in "$$DIR"/*; do \
		[ -f "$$f" ] || continue; \
		total=$$((total + 1)); \
		base=$$(basename "$$f"); \
		out=test_dummy; \
		printf "=== %s ===\n" "$$base" >> "$$LOG"; \
		output=$$(./ccomp "$$f" -o "$$out" 2>&1); \
		exit_code=$$?; \
		if [ $$exit_code -eq 0 ]; then \
			printf "[%s] SUCCESS: %s -> %s\n%s\n\n" "$$(date)" "$$f" "$$out" "$$output" >> "$$LOG"; \
			echo "OK: $$base"; \
			succ=$$((succ + 1)); \
		else \
			printf "[%s] FAILURE: %s (exit code %d)\n%s\n\n" "$$(date)" "$$f" "$$exit_code" "$$output" >> "$$LOG"; \
			echo "FAIL: $$base"; \
			fail=$$((fail + 1)); \
			rm -f "$$out" >/dev/null 2>&1; \
		fi; \
	done; \
	printf "\nSummary: total=%d success=%d fail=%d\n" $$total $$succ $$fail | tee -a "$$LOG"

-include .depend

FORCE:
