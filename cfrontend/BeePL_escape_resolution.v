(* Relate the conservative guard's first-match resolver to the actual source
   global environment. Uniqueness is derived from acceptance, not assumed of
   arbitrary raw declaration lists. *)
Require Import List String Bool Coqlib Maps AST Globalenvs BeeTypes BeePL.
Require Import BeePL_escape_check.
Import ListNotations.

Lemma escape_program_global_identifiers_unique : forall p,
  escape_program_check p=true ->
  list_norepet(map(fun '(id,_,_)=>id)(prog_defs p)).
Proof.
  intros p H. unfold escape_program_check in H.
  apply andb_true_iff in H as [H _].
  destruct(list_norepet_dec ident_eq (map(fun '(id,_,_)=>id)(prog_defs p)));
    [assumption|discriminate].
Qed.

Lemma escape_lookup_function_member : forall defs id fd,
  escape_lookup_function id defs=Some fd ->
  exists section, In(id,@Gfun BeePL.fundef BeeTypes.type fd,section)defs.
Proof.
  induction defs as [|[[name gd] section] rest IH]; intros id fd H; simpl in H;
    [discriminate|].
  destruct(ident_eq id name) as [E|E].
  - subst name. destruct gd; try discriminate. inversion H; subst.
    exists section; left; reflexivity.
  - destruct(IH _ _ H) as [s Hin]. exists s; right; exact Hin.
Qed.

Lemma escape_lookup_function_member_unique : forall defs id fd section,
  list_norepet(map(fun '(name,_,_)=>name)defs) ->
  In(id,@Gfun BeePL.fundef BeeTypes.type fd,section)defs -> escape_lookup_function id defs=Some fd.
Proof.
  induction defs as [|[[name gd] sec] rest IH]; intros id fd section Hunique Hin;
    [contradiction|].
  inversion Hunique as [|? ? Hfresh Htail]; subst.
  destruct Hin as [E|Hin].
  - inversion E; subst. simpl. destruct(ident_eq id id); congruence.
  - simpl. destruct(ident_eq id name) as [E|E].
    + subst name. exfalso. apply Hfresh.
      change (In ((fun '(name,_,_)=>name)(id,@Gfun BeePL.fundef BeeTypes.type fd,section))
        (map(fun '(name,_,_)=>name)rest)). apply in_map; exact Hin.
    + eapply IH; eauto.
Qed.

Lemma source_ast_global_names : forall p,
  AST.prog_defs_names (trans_program_astprog p)=
    map(fun '(id,_,_)=>id)(prog_defs p).
Proof.
  intros. unfold AST.prog_defs_names,trans_program_astprog; simpl.
  rewrite map_map. apply map_ext. intros [[id gd] section]; reflexivity.
Qed.

Theorem accepted_resolver_matches_global_definition : forall p id fd,
  escape_program_check p=true ->
  (escape_lookup_function id (prog_defs p)=Some fd <->
   exists b, Genv.find_symbol (BeePL.globalenv p) id=Some b /\
     Genv.find_def (BeePL.globalenv p) b=Some(@Gfun BeePL.fundef BeeTypes.type fd)).
Proof.
  intros p id fd Hcheck.
  change (escape_lookup_function id (prog_defs p)=Some fd <->
   exists b, Genv.find_symbol (Genv.globalenv(trans_program_astprog p)) id=Some b /\
     Genv.find_def (Genv.globalenv(trans_program_astprog p)) b=Some(@Gfun BeePL.fundef BeeTypes.type fd)).
  rewrite <- Genv.find_def_symbol. split.
  - intros Hlookup. destruct(escape_lookup_function_member _ _ _ Hlookup) as [sec Hin].
    apply AST.prog_defmap_norepet.
    + rewrite source_ast_global_names. apply escape_program_global_identifiers_unique; exact Hcheck.
    + change (In(id,@Gfun BeePL.fundef BeeTypes.type fd)(map(fun '(name,gd,_) => (name,gd))(prog_defs p))).
      change (In ((fun '(name,gd,_) => (name,gd))(id,@Gfun BeePL.fundef BeeTypes.type fd,sec))
        (map(fun '(name,gd,_) => (name,gd))(prog_defs p))).
      apply in_map; exact Hin.
  - intros Hlookup. apply AST.in_prog_defmap in Hlookup.
    change (In(id,@Gfun BeePL.fundef BeeTypes.type fd)(map(fun '(name,gd,_) => (name,gd))(prog_defs p))) in Hlookup.
    apply in_map_iff in Hlookup as [[[name gd] sec] [E Hin]].
    inversion E; subst. eapply escape_lookup_function_member_unique; eauto.
    apply escape_program_global_identifiers_unique; exact Hcheck.
Qed.

Corollary accepted_resolver_matches_function_pointer : forall p id fd,
  escape_program_check p=true ->
  escape_lookup_function id (prog_defs p)=Some fd ->
  exists b, Genv.find_symbol (BeePL.globalenv p) id=Some b /\
    Genv.find_funct_ptr (BeePL.globalenv p) b=Some fd.
Proof.
  intros p id fd Hcheck Hlookup.
  apply (accepted_resolver_matches_global_definition _ _ _ Hcheck) in Hlookup.
  destruct Hlookup as [b [Hsymbol Hdef]]. exists b; split; auto.
  apply Genv.find_funct_ptr_iff; exact Hdef.
Qed.

Print Assumptions accepted_resolver_matches_global_definition.
Print Assumptions accepted_resolver_matches_function_pointer.
