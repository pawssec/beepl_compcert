(* Initial global memory is identical for an actual successful translation.
   This says nothing about source/target local allocations during execution. *)
Require Import List String ZArith Coqlib Errors Maps AST Memory Globalenvs Ctypes Csyntax.
Require Import BeeTypes BeePL BeePL_Csyntax BeePL_compiler_globals.

Section INITIAL_MEMORY.
Variables (p : BeePL.program) (cp : Csyntax.program).
Variable names : list (ident * string).
Variable sections : list (ident * csyntax_atom_info).
Hypothesis translated : BeePL_compcert p = OK (cp,names,sections).

Lemma compiled_initializer_data : forall datum m b offset,
 Genv.store_init_data (Genv.globalenv cp) m b offset datum =
 Genv.store_init_data (Genv.globalenv (trans_program_astprog p)) m b offset datum.
Proof.
 intros datum m b offset. destruct datum; simpl; try reflexivity.
 rewrite (compiler_symbols_preserved _ _ _ _ translated); reflexivity.
Qed.

Lemma compiled_initializer_list : forall data m b offset,
 Genv.store_init_data_list (Genv.globalenv cp) m b offset data =
 Genv.store_init_data_list (Genv.globalenv (trans_program_astprog p)) m b offset data.
Proof.
 induction data as [|datum rest IH]; intros m b offset; simpl; [reflexivity|].
 rewrite compiled_initializer_data.
 destruct (Genv.store_init_data (Genv.globalenv (trans_program_astprog p)) m b offset datum);
 [apply IH|reflexivity].
Qed.

Lemma compiled_global_allocation : forall id source target m,
 lowered_global p.(prog_comp_env) source target ->
 Genv.alloc_global (Genv.globalenv cp) m (id,target) =
 Genv.alloc_global (Genv.globalenv (trans_program_astprog p)) m (id,source).
Proof.
 intros id source target m H. inversion H; subst; [reflexivity|].
 destruct gv as [ty init readonly volatile].
 cbn [transBeePLglobvar_globvar fst Genv.alloc_global AST.gvar_init].
 destruct (Mem.alloc m 0 (init_data_list_size init)) as [allocated block].
 destruct (store_zeros allocated block 0 (init_data_list_size init)); [|reflexivity].
 rewrite compiled_initializer_list. reflexivity.
Qed.

Lemma compiled_globals_allocation : forall source target,
 list_forall2 (fun a b => fst a=fst b /\ lowered_global p.(prog_comp_env) (snd a) (snd b)) source target ->
 forall m, Genv.alloc_globals (Genv.globalenv cp) m target =
 Genv.alloc_globals (Genv.globalenv (trans_program_astprog p)) m source.
Proof.
 intros source target H. induction H as [|[id gd] rest [tid tgd] trest Hhead Htail IH];
 intros m; [reflexivity|].
 destruct Hhead as [E Hgd]; simpl in E,Hgd; subst tid.
 change ((match Genv.alloc_global (Genv.globalenv cp) m (id,tgd) with
 | Some next => Genv.alloc_globals (Genv.globalenv cp) next trest
 | None => None end) =
 (match Genv.alloc_global (Genv.globalenv (trans_program_astprog p)) m (id,gd) with
 | Some next => Genv.alloc_globals (Genv.globalenv (trans_program_astprog p)) next rest
 | None => None end)).
 rewrite (compiled_global_allocation id gd tgd m Hgd).
 destruct (Genv.alloc_global (Genv.globalenv (trans_program_astprog p)) m (id,gd)); [apply IH|reflexivity].
Qed.

Theorem compiler_initial_memory_preserved :
 Genv.init_mem cp = Genv.init_mem (trans_program_astprog p).
Proof.
 unfold Genv.init_mem.
 apply compiled_globals_allocation.
 eapply successful_compiler_global_definitions; exact translated.
Qed.
End INITIAL_MEMORY.
Print Assumptions compiler_initial_memory_preserved.
