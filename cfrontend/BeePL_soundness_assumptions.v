(* Run afresh with `make soundness-check`. The shell gate checks the dependency
   assumptions of these exact public results, including a real loaded witness.
   This file is a coqtop audit input, not an additional theorem assumption. *)
Require Import BeePL_typesystem_proofs BeePL_initial_program_execution.
Require Import BeePL_initial_program BeePL_program_multistep.

Print Assumptions program_expression_soundness.
Print Assumptions program_expression_progress_checked.
Print Assumptions program_expression_preservation_checked.
Print Assumptions program_list_step_preservation.
Print Assumptions program_closure_preservation.
Print Assumptions program_closures_preservation.
Print Assumptions program_closure_normal_form_is_typed_value.
Print Assumptions program_reaches_cannot_get_stuck.
Print Assumptions program_closures_values_or_progress.
Print Assumptions initial_code_configuration.
Print Assumptions internal_source_loaded_configuration.
Print Assumptions loaded_entry_configuration.
Print Assumptions loaded_entry_takes_step.
Print Assumptions entry_program_checked.
