(* Leaf cases of the whole-expression induction. Ebytes has no declarative
   typing rule; packet Bytes values themselves are covered by Val. *)
Require Import List Integers AST Maps Memory Ctypes.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_auxlemmas.
Require Import BeePL_program_runtime BeePL_program_induction BeePL_program_control_cases.
Require Import BeePL_initialized_runtime BeePL_initialized_configurations.
Require Import BeePL_coherent_configurations BeePL_coherent_literals BeePL_coherent_option_cases.
Require Import BeePL_general_named_array_reads.
Import ListNotations.

Theorem program_value_case : forall v ty,program_expression_safe(Val v ty).
Proof.
 intros v ty;split;unfold program_expression_progress,program_expression_preservation.
 - intros * Hconfig;left;do 2 eexists;reflexivity.
 - intros * Hconfig Hstep;inversion Hstep.
Qed.

Theorem program_ebytes_case : forall es ty,program_expression_safe(Ebytes es ty).
Proof.
 intros es ty;split;unfold program_expression_progress,program_expression_preservation;intros * [Hcode [[Hheap Htyped Hloc Hframes] Hcoherent]];inversion Htyped.
Qed.

Theorem program_constant_case : forall c rt,program_expression_safe(Const c rt).
Proof.
 intros c rt;program_case_start.
 - right. destruct(coherent_constant_progress _ _ _ _ _ _ _ _ p _ _ _ Hconfig) as [v [Hstep Hrest]]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   match goal with Hs:ssem_expr _ _ _ _ _ _ _ _ |- _ =>
    destruct(coherent_constant_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hs) as [Hm [Hvm [Hevolve Hnew]]] end.
   do 4 eexists; eexists;split;[exact Hevolve|]. split;[exact Hnew|apply sub_effect_refl].
Qed.

Theorem program_unit_case : forall rt,program_expression_safe(Unit rt).
Proof.
 intros rt;program_case_start.
 - right. destruct(coherent_unit_progress _ _ _ _ _ _ _ _ p _ _ Hconfig) as [Hstep Hrest]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   match goal with Hs:ssem_expr _ _ _ _ _ _ _ _ |- _ =>
    destruct(coherent_unit_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hs) as [Hm [Hvm [Hevolve Hnew]]] end.
   do 4 eexists;eexists;split;[exact Hevolve|]. split;[exact Hnew|apply sub_effect_refl].
Qed.

Theorem program_address_case : forall loc ofs rt,program_expression_safe(Addr loc ofs rt).
Proof.
 intros loc ofs rt;program_case_start.
 - right. destruct(coherent_address_progress _ _ _ _ _ _ _ _ p _ _ _ _ Hconfig) as [Hstep Hrest]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   match goal with Hs:ssem_expr _ _ _ _ _ _ _ _ |- _ =>
    destruct(coherent_address_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hs) as [Hm [Hvm [Hevolve Hnew]]] end.
   do 4 eexists;eexists;split;[exact Hevolve|]. split;[exact Hnew|apply sub_effect_refl].
Qed.

Theorem program_none_case : forall rt,program_expression_safe(Enone rt).
Proof.
 intros rt;program_case_start.
 - right. destruct(coherent_none_progress _ _ _ _ _ _ _ _ p _ _ Hconfig) as [result [Hstep Hrest]]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   eapply coherent_none_preservation;[exact Hconfig|eassumption].
Qed.

Theorem program_variable_case : forall x rt,program_expression_safe(Var x rt).
Proof.
 intros x rt;program_case_start.
 - right. destruct(initialized_variable_configuration_progress _ _ _ _ _ _ _ _ p _ _ _ (proj1 Hconfig)) as [v [Hstep Hrest]]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   match goal with Hs:ssem_expr _ _ _ _ _ _ _ _ |- _ =>
     pose proof(initialized_variable_configuration_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 Hconfig) Hs) as Hnew;
     assert(Hm: final=m) by (inversion Hs;reflexivity)
   end. subst final.
   do 4 eexists;eexists;split;[eapply initialized_heap_evolution_refl;exact Hheap|].
   split;[split;[exact Hnew|exact Hcoherent]|apply sub_effect_refl].
Qed.

Theorem program_named_array_case : forall x arr n rt,program_expression_safe(Aaccess x arr n rt).
Proof.
 intros x arr n rt;program_case_start.
 all: assert(Hshape:exists len attr,arr=Atype ty len attr).
 all: try solve [inversion Htyped;subst;match goal with Hs:exists len attr, _ /\ _ |- _ => destruct Hs as [len [attr [Heq Hb]]];eauto end].
 all: destruct Hshape as [len [attr Heq]];subst arr.
 - right. destruct(coherent_named_array_read_progress _ _ _ _ _ _ _ _ p _ _ _ _ _ _ Hconfig)
   as [value [objects' [Hstep Hrest]]]. do 3 eexists;exact Hstep.
 - eapply program_result_lift;[eassumption|].
   match goal with Hs:ssem_expr _ _ _ _ _ _ _ _ |- _ =>
     destruct(coherent_named_array_read_preservation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hconfig Hs)
     as [Hm [Hvm [objects' [Hevolve Hnew]]]] end.
   do 4 eexists;eexists;split;[exact Hevolve|]. split;[exact Hnew|apply sub_effect_refl].
Qed.
