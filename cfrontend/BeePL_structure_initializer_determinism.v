(* Real program layouts have full-width fields. Their actual initializer
   executions are functional, including aggregate and descriptor copies. *)
Require Import List ZArith Lia Coqlib Integers AST Maps Memory Ctypes Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.
Require Import BeePL_layout_proofs BeePL_structure_storage_typing BeePL_initializer_determinism BeePL_strict_progress.
Import ListNotations.

Lemma plain_source_field_offset_full : forall members env field pos delta bf,
 Forall bmember_is_plain members ->
 field_offset_rec env field(bmembers_cmembers members) pos=OK(delta,bf) -> bf=Full.
Proof.
 induction members as [|member members IH];intros * Hplain Hoffset;[discriminate|].
 inversion Hplain;subst. destruct member;[|contradiction]. simpl in Hoffset.
 destruct(ident_eq field i);[inversion Hoffset;reflexivity|eapply IH;eauto].
Qed.

Lemma program_field_offset_full : forall p sid co field delta bf,
 PTree.get sid p.(prog_comp_env)=Some co ->
 field_offset(bcomposite_composite_env p.(prog_comp_env)) field(bmembers_cmembers co.(co_members))=OK(delta,bf) ->
 bf=Full.
Proof.
 intros * Hco Hoffset. eapply plain_source_field_offset_full;
 [exact(proj2(program_composite_shape p sid co Hco))|exact Hoffset].
Qed.

Theorem structure_fields_unique : forall p block base sid fields values types m first,
 sem_allocate_fields(globalenv p) block base sid fields values types m first ->
 forall second,sem_allocate_fields(globalenv p) block base sid fields values types m second ->first=second.
Proof.
 intros * Hfirst;induction Hfirst;intros second Hsecond;inversion Hsecond;subst;auto.
 assert(Hfull:bf=Full) by(exact(program_field_offset_full p sid co f delta bf H H0)).
 subst bf.
 match goal with Hco1:PTree.get _ _=Some ?co1,Hco2:PTree.get _ _=Some ?co2 |- _ =>
 tryif constr_eq co1 co2 then fail else (assert(co1=co2) by congruence;subst co2) end.
 match goal with Hoffset1:field_offset _ _ _=OK(?d1,_),Hoffset2:field_offset _ _ _=OK(?d2,_) |- _ =>
 tryif constr_eq d1 d2 then fail else (assert(d1=d2) by congruence;subst d2) end.
 match goal with Hoffset:field_offset _ _ _=OK(_,?bf) |- _ =>
  tryif constr_eq bf Full then fail else
   (assert(bf=Full) by congruence;subst bf)
 end.
 match goal with Hassign1:assign_addr _ _ _ _ _ Full _ ?next1 _,
 Hassign2:assign_addr _ _ _ _ _ Full _ ?next2 _ |- _ =>
 tryif constr_eq next1 next2 then fail else (destruct(full_assignment_unique _ _ _ _ _ _ _ _ _ _ Hassign1 Hassign2) as [Heq _];subst next2) end.
 eapply IHHfirst;eauto.
Qed.

Theorem evaluated_structure_step_unique : forall p vm m sid ids es result first vm1 e1 second vm2 e2,
 Forall(fun e=>exists v ty,e=Val v ty) es ->
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) first vm1 e1 ->
 ssem_expr(globalenv p) p vm m(Sinit sid ids es result) second vm2 e2 ->
 first=second /\ vm1=vm2 /\ e1=e2.
Proof.
 intros * Hvalues Hfirst Hsecond.
 pose proof(all_value_arguments_is_values _ Hvalues) as Hready.
 inversion Hfirst;subst;[congruence|]. inversion Hsecond;subst;[congruence|].
 match goal with Hshape1:structure_result_type sid ?a1 result,Hshape2:structure_result_type sid ?a2 result |- _ =>
 assert(a1=a2) by(eapply structure_result_attribute_unique;eauto);subst a2 end.
 match goal with Ha1:Mem.alloc _ _ _=(?allocated1,?fresh1),Ha2:Mem.alloc _ _ _=(?allocated2,?fresh2) |- _ =>
 let Hsame:=fresh "Hsame" in
 assert(Hsame:allocated1=allocated2 /\ fresh1=fresh2) by(split;congruence);destruct Hsame as [Hm Hb];subst allocated2 fresh2 end.
 split;[eapply structure_fields_unique;eauto|]. split;reflexivity.
Qed.

Print Assumptions structure_fields_unique.
Print Assumptions evaluated_structure_step_unique.
