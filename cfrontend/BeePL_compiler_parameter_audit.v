(* Before the repair, lowering could collide with a source parameter:
   fresh_ident reserved local declarations but omitted ordinary parameters.
   This regression checks that the repaired reservation excludes that collision. *)
Require Import List String ZArith Coqlib Integers AST Maps Ctypes Csyntax Ctypesdefs SimplExpr Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_typesystem BeePL_typechecker BeePL_Csyntax.
Import ListNotations.
Definition collision_int := Vtype (BeeTypes.Tint I32 Signed noattr).
Definition collision_ref := Ptrtype(Reftype(Bprim(BeeTypes.Tint I32 Signed noattr)) noattr).
Definition collision_parameter := ident_of_string "__fresh__1000".
Definition collision_function : BeePL.function :=
 {| BeePL.fn_return:=collision_int; fn_effect:=[Alloc]; fn_callconv:=cc_default;
    fn_args:=[(collision_parameter,collision_int)]; fn_vars:=[];
    fn_body:=Bind (ident_of_string "_") collision_ref
      (Prim Ref [Const(ConsInt Int.one) collision_int] collision_ref)
      (Const(ConsInt Int.zero) collision_int) collision_int;
    is_ebpf:=false |}.
Definition collision_context : bcompiler_ctx :=
 {| arg_ctx:=[]; benv:=PTree.empty _; reserved_identifiers:=[]; lexical_bindings:=BeePL_compiler_bindings.empty_compiler_bindings |}.

Lemma collision_function_checked : exists message,
 type_check_function (PTree.empty _) (PTree.empty _) (PTree.empty _) collision_function=OK message.
Proof. eexists; reflexivity. Qed.

Lemma collision_source_names_distinct :
 NoDup(map fst(BeePL.fn_args collision_function) ++ map fst(BeePL.fn_vars collision_function)).
Proof. constructor; [simpl; tauto|constructor]. Qed.

Theorem successful_lowering_reserves_parameter : exists cf names ctx,
 transBeePL_function_function (PTree.empty _) collision_function [] collision_context=OK(cf,names,ctx) /\
 map fst(Csyntax.fn_params cf)=[collision_parameter] /\
 map fst(Csyntax.fn_vars cf)=[ident_of_string "__fresh__998"; ident_of_string "__fresh__999"] /\
 NoDup(map fst(Csyntax.fn_params cf) ++ map fst(Csyntax.fn_vars cf)).
Proof.
 eexists; eexists; eexists; split; [vm_compute; reflexivity|].
 split; [reflexivity|]. split; [reflexivity|].
 change (NoDup[collision_parameter;ident_of_string "__fresh__998";ident_of_string "__fresh__999"]).
 constructor; [simpl; intros [H|[H|H]]; [discriminate H|discriminate H|contradiction]|].
 constructor; [simpl; intros [H|H]; [discriminate H|contradiction]|].
 constructor; [simpl; tauto|constructor].
Qed.
Print Assumptions collision_function_checked.
Print Assumptions successful_lowering_reserves_parameter.
