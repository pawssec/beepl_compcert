(* A real loaded internal function and a nonterminal source entry.  This is an
   inhabitation regression, not general adequacy for data globals or helpers. *)
Require Import List String ZArith Integers AST Maps Memory Ctypes Globalenvs Errors Coqlib.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_typechecker.
Require Import BeePL_initial_program BeePL_program_runtime BeePL_runtime_locations.
Require Import BeePL_packet_bindings BeePL_frame_free BeePL_general_application.
Import ListNotations.
Local Open Scope list_scope.

Definition entry_int := Vtype (Tint I32 Signed noattr).
Definition entry_body := Cond (Val (Vbool true) (Vtype Tbool))
  (Val (Vint (Int.repr 41)) entry_int) (Val (Vint Int.zero) entry_int) entry_int.
Definition entry_function : function :=
  {| fn_return := entry_int; fn_effect := []; fn_callconv := cc_default;
     fn_args := []; fn_vars := []; fn_body := entry_body; is_ebpf := false |}.
Lemma entry_composites_wf : wf_bcomposites [].
Proof. vm_compute. exact I. Qed.
Definition entry_program : program := @mkbprogram []
  [(1%positive, Gfun (Internal entry_function), None)] [1%positive] 1%positive entry_composites_wf [].
Definition entry_expression := App (Val (Vloc 1%positive Ptrofs.zero)
  (type_of_function entry_function)) [] entry_int.

Lemma entry_body_typed : forall cenv Gamma Sigma,
  type_expr cenv Gamma Sigma entry_body [] entry_int.
Proof.
  intros. change ([] : effect) with (([] : effect) ++ []). unfold entry_body.
  eapply ty_cond with (ef1:=[]) (ef2:=[]) (ef3:=[]) (branch_effect:=[]);
    try apply ty_valb; try apply ty_vali; reflexivity.
Qed.
Lemma entry_function_typed : forall cenv Gamma Sigma,
  type_function cenv Gamma Sigma entry_function.
Proof. intros. eapply ty_function with (ef:=[]) (tb:=entry_int) (Gamma':=Gamma);
  try reflexivity.
  - constructor.
  - apply entry_body_typed.
Qed.
Lemma entry_program_typed : type_program entry_program.
Proof.
  eapply ty_prog; [reflexivity|reflexivity|reflexivity|].
  constructor; [|constructor]. eapply ty_fundef; [reflexivity|].
  eapply ty_ifundef; [reflexivity|apply entry_function_typed].
Qed.
Lemma entry_program_checked : exists message, type_check_program entry_program = OK message.
Proof. vm_compute. eexists; reflexivity. Qed.
Lemma entry_symbol : Genv.find_symbol (globalenv entry_program) 1%positive = Some 1%positive.
Proof. vm_compute; reflexivity. Qed.
Lemma entry_code : Genv.find_funct (globalenv entry_program)
  (Values.Vptr 1%positive Ptrofs.zero) = Some (Internal entry_function).
Proof. vm_compute; reflexivity. Qed.
Lemma entry_only_code : forall b fn,
  Genv.find_funct (globalenv entry_program) (Values.Vptr b Ptrofs.zero) = Some (Internal fn) ->
  fn = entry_function.
Proof.
  intros b fn Hfind. rewrite Genv.find_funct_find_funct_ptr in Hfind.
  destruct (Genv.find_funct_ptr_inversion _ _ Hfind) as [id Hin].
  simpl in Hin. destruct Hin as [Heq|Hfalse]; [inversion Heq; reflexivity|contradiction].
Qed.
Lemma entry_globals_resolved : resolved_internal_globals (globalenv entry_program) (source_globals entry_program).
Proof.
  intros id ty Hget. change ((PTree.set 1%positive (type_of_function entry_function) empty_context) ! id = Some ty) in Hget.
  rewrite PTree.gsspec in Hget. destruct (peq id 1%positive); subst.
  - inversion Hget; subst. exists 1%positive,entry_function. auto using entry_symbol,entry_code.
  - rewrite PTree.gempty in Hget; discriminate.
Qed.
Lemma entry_expression_typed : type_expr entry_program.(prog_comp_env)
  (source_globals entry_program) empty_stcontext entry_expression [] entry_int.
Proof.
  unfold entry_expression, type_of_function; simpl.
  eapply ty_app with (ef:=[]) (efs:=[]) (efs':=[]) (ts:=[]) (v:=false);
    try reflexivity; constructor.
Qed.

Theorem loaded_entry_configuration : exists m,
  Genv.init_mem (trans_program_astprog entry_program) = Some m /\
  program_runtime_configuration entry_program (source_globals entry_program)
    (source_globals entry_program) empty_stcontext empty_vmap m
    initial_no_objects initial_no_cells initial_no_packets entry_expression [] entry_int.
Proof.
  destruct (code_only_loader_exists entry_program) as [m Hload].
  { intros id gv Hin. simpl in Hin. destruct Hin as [H|H]; [discriminate|contradiction]. }
  exists m; split; [exact Hload|]. eapply initial_code_configuration.
  - exact entry_program_typed.
  - reflexivity.
  - exact entry_globals_resolved.
  - intros b fn Hfind. apply entry_only_code in Hfind; subst fn. simpl. repeat split.
  - exact entry_expression_typed.
  - change ((packet_heap_locations (globalenv entry_program) initial_no_cells initial_no_objects initial_no_packets)
      1%positive Ptrofs.zero (type_of_function entry_function) /\ True).
    split; [|exact I]. apply packet_callable_embedding. split; [reflexivity|].
    unfold type_of_function; repeat eexists; eauto using entry_code.
  - simpl; auto.
Qed.

Theorem loaded_entry_takes_step : exists m final vm next,
  Genv.init_mem (trans_program_astprog entry_program) = Some m /\
  ssem_expr (globalenv entry_program) entry_program empty_vmap m entry_expression final vm next.
Proof.
  destruct loaded_entry_configuration as [m [Hload Hconfig]].
  destruct (general_application_progress entry_program (source_globals entry_program)
    (source_globals entry_program) empty_stcontext empty_vmap m initial_no_objects initial_no_cells
    initial_no_packets (Vloc 1%positive Ptrofs.zero) (type_of_function entry_function) [] entry_int []
    Hconfig (Forall_nil _)) as [final [vm [next Hstep]]].
  exists m,final,vm,next; auto.
Qed.
Print Assumptions loaded_entry_configuration.
Print Assumptions loaded_entry_takes_step.
