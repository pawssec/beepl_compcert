(* Checked global correspondence for actual successful lowering. This uses the
   executable fundef translator, not the legacy small expression-simulation
   relation, and never relates arbitrary unrelated global environments. *)
Require Import Program.Equality Program.Tactics List String Coqlib Errors Maps AST Globalenvs Ctypes Csyntax Csem.
Require Import BeeTypes BeePL BeePL_Csyntax BeePL_Check_Reserved_Struct.
Require Import BeePL_escape_check.
Require Import BeePL_representation_check.
Import ListNotations.

Definition lowered_fundef (env : bcomposite_env) (f : BeePL.fundef) (tf : Csyntax.fundef) : Prop :=
 exists names ctx names' ctx',
 transBeePL_fundef_fundef env f names ctx = OK (tf,names',ctx').

Inductive lowered_global (env : bcomposite_env) :
 AST.globdef BeePL.fundef BeeTypes.type -> AST.globdef Csyntax.fundef Ctypes.type -> Prop :=
| lowered_function : forall f tf, lowered_fundef env f tf -> lowered_global env (Gfun f) (Gfun tf)
| lowered_variable : forall gv,
 lowered_global env (Gvar gv) (Gvar (fst (transBeePLglobvar_globvar gv))).

Lemma successful_global_lowering : forall env gd names ctx out names' comps ctx',
 transBeePL_globdef_globdef env gd names ctx = OK(out,names',comps,ctx') ->
 lowered_global env gd out.
Proof.
 intros env [f|gv] names ctx out names' comps ctx' H; simpl in H.
 - destruct(transBeePL_fundef_fundef env f names ctx) as [[[tf ns] cx]|msg] eqn:E;
   simpl in H; try discriminate. inversion H; subst. constructor.
   repeat eexists; exact E.
 - inversion H; subst. constructor.
Qed.

Lemma successful_globals_lowering : forall env gds names ctx out names' comps ctx',
 transBeePL_globdefs_globdefs env gds names ctx = OK(out,names',comps,ctx') ->
 list_forall2 (lowered_global env) gds out.
Proof.
 intros env gds; induction gds as [|gd rest IH]; intros names ctx out names' comps ctx' H; simpl in H.
 - inversion H; constructor.
 - destruct(transBeePL_globdef_globdef env gd names ctx) as [[[[tg ns] cs] cx]|msg] eqn:E;
   simpl in H; try discriminate.
   destruct(transBeePL_globdefs_globdefs env rest ns cx) as [[[[tail ns'] cs'] cx']|msg] eqn:F;
   simpl in H; try discriminate. inversion H; subst.
   constructor; [eapply successful_global_lowering; exact E|eapply IH; exact F].
Qed.

Lemma lowered_global_environments : forall env
 (p : AST.program BeePL.fundef BeeTypes.type) (tp : AST.program Csyntax.fundef Ctypes.type),
 list_forall2 (fun a b => fst a=fst b /\ lowered_global env (snd a) (snd b))
   (AST.prog_defs p) (AST.prog_defs tp) ->
 Genv.match_genvs (lowered_global env) (Genv.globalenv p) (Genv.globalenv tp).
Proof.
 intros env p tp H. unfold Genv.globalenv. apply Genv.add_globals_match; [exact H|].
 constructor; simpl; auto. intros; rewrite !PTree.gempty; constructor.
Qed.

Theorem lowered_symbols_preserved : forall env p tp,
 list_forall2 (fun a b => fst a=fst b /\ lowered_global env (snd a) (snd b))
   (AST.prog_defs p) (AST.prog_defs tp) ->
 forall id, Genv.find_symbol (Genv.globalenv tp) id=Genv.find_symbol (Genv.globalenv p) id.
Proof. intros env p tp H id. exact (Genv.mge_symb (lowered_global_environments _ _ _ H) id). Qed.

Theorem lowered_function_pointer_preserved : forall env p tp,
 list_forall2 (fun a b => fst a=fst b /\ lowered_global env (snd a) (snd b))
   (AST.prog_defs p) (AST.prog_defs tp) ->
 forall b f, Genv.find_funct_ptr(Genv.globalenv p) b=Some f ->
 exists tf, Genv.find_funct_ptr(Genv.globalenv tp) b=Some tf /\ lowered_fundef env f tf.
Proof.
 intros env p tp H b f Hfind.
 pose proof (Genv.mge_defs (lowered_global_environments _ _ _ H) b) as Hr.
 apply Genv.find_funct_ptr_iff in Hfind. unfold Genv.find_def in Hfind.
 rewrite Hfind in Hr. inversion Hr; subst.
 inversion H2; subst. eexists; split.
 - apply Genv.find_funct_ptr_iff. unfold Genv.find_def. symmetry; exact H1.
 - eassumption.
Qed.

Theorem lowered_function_preserved : forall env p tp,
 list_forall2 (fun a b => fst a=fst b /\ lowered_global env (snd a) (snd b))
   (AST.prog_defs p) (AST.prog_defs tp) ->
 forall v f, Genv.find_funct(Genv.globalenv p) v=Some f ->
 exists tf, Genv.find_funct(Genv.globalenv tp) v=Some tf /\ lowered_fundef env f tf.
Proof.
 intros env p tp H v f Hfind.
 destruct(Genv.find_funct_inv _ _ Hfind) as [b Hv]; subst v.
 rewrite Genv.find_funct_find_funct_ptr in *.
 eapply lowered_function_pointer_preserved; eauto.
Qed.
Print Assumptions lowered_function_preserved.

Lemma lowered_zip_identifiers : forall env (defs : list (ident * AST.globdef BeePL.fundef BeeTypes.type)) outs,
 list_forall2 (lowered_global env) (seq.unzip2 defs) outs ->
 list_forall2 (fun a b => fst a=fst b /\ lowered_global env (snd a) (snd b))
 defs (seq.zip (seq.unzip1 defs) outs).
Proof.
 intros env defs; induction defs as [|[id gd] rest IH]; intros outs H;
 inversion H; subst; simpl; constructor; auto.
Qed.

Lemma made_program_definitions : forall cs defs pubs main cp,
 @Ctypes.make_program Csyntax.function cs defs pubs main=OK cp ->
 AST.prog_defs cp=defs.
Proof.
 intros cs defs pubs main cp. unfold Ctypes.make_program.
 generalize (eq_refl (Ctypes.build_composite_env cs)).
 generalize (Ctypes.build_composite_env cs) at 1 3.
 intros r E H. destruct r; inversion H; reflexivity.

Qed.

Theorem successful_compiler_global_definitions : forall p cp names sections,
 BeePL_compcert p=OK(cp,names,sections) ->
 list_forall2 (fun a b => fst a=fst b /\ lowered_global p.(prog_comp_env) (snd a) (snd b))
 (AST.prog_defs(trans_program_astprog p)) (AST.prog_defs cp).
Proof.
 intros p cp names sections H. unfold BeePL_compcert in H.
 destruct(check_struct_from_program p) eqn:Echeck; simpl in H; try discriminate.
 destruct(check_compiler_representation p) eqn:Erepresentation; simpl in H; try discriminate.
 destruct(check_reference_escapes p) eqn:Eescape; simpl in H; try discriminate.
 destruct(transBeePL_globdefs_globdefs _ _ _ _) as [[[[outs ns] extra] ctx]|msg] eqn:Edefs;
 simpl in H; try discriminate.
 destruct(Ctypes.make_program _ _ _ _) as [made|msg] eqn:Emade;
 simpl in H; try discriminate.
 inversion H; subst.
 apply made_program_definitions in Emade. rewrite Emade.
 apply lowered_zip_identifiers. eapply successful_globals_lowering; exact Edefs.
Qed.

Theorem compiler_symbols_preserved : forall p cp names sections,
 BeePL_compcert p=OK(cp,names,sections) -> forall id,
 Genv.find_symbol (Genv.globalenv cp) id=Genv.find_symbol (BeePL.globalenv p) id.
Proof.
 intros p cp names sections H id.
 eapply lowered_symbols_preserved; eapply successful_compiler_global_definitions; exact H.
Qed.

Theorem compiler_functions_preserved : forall p cp names sections,
 BeePL_compcert p=OK(cp,names,sections) -> forall v f,
 Genv.find_funct (BeePL.globalenv p) v=Some f -> exists tf,
 Genv.find_funct (Genv.globalenv cp) v=Some tf /\ lowered_fundef p.(prog_comp_env) f tf.
Proof.
 intros p cp names sections H v f Hfind. eapply lowered_function_preserved; [|exact Hfind].
 eapply successful_compiler_global_definitions; exact H.
Qed.
Print Assumptions compiler_symbols_preserved.
Print Assumptions compiler_functions_preserved.
