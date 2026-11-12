(* Packet pattern instantiation removes exactly the names bound by its chosen
   branch; this is independent of the packet contents or heap typing. *)
Require Import List ZArith Integers AST Maps Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_packet BeePL_substitution_freevars.
Require Import BeePL_match_arity.
Import ListNotations.

Lemma instantiate_fields_arity : forall fields values body result,
  instantiate_field_values fields values body=OK result -> match_arity result=match_arity body.
Proof.
  induction fields as [|[name ty] fields IH]; intros values body result H;
    destruct values as [|v values]; simpl in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (instantiate_field_values fields values body) as [next|error] eqn:Hnext; try discriminate.
    inversion H; subst. rewrite value_substitution_preserves_match_arity. eapply IH; exact Hnext.
Qed.

Lemma instantiate_fields_freevars : forall fields values body result,
  match_arity body=true -> instantiate_field_values fields values body=OK result ->
  incl (free_variables result)
    (fold_right (fun x rest=>remove ident_eq x rest) (free_variables body) (List.map fst fields)).
Proof.
  induction fields as [|[name ty] fields IH]; intros values body result Hvalid H;
    destruct values as [|v values]; simpl in H; try discriminate.
  - inversion H; subst; apply incl_refl.
  - destruct (instantiate_field_values fields values body) as [next|error] eqn:Hnext; try discriminate.
    inversion H; subst. simpl.
    eapply incl_tran; [apply arity_value_substitution_removes_variable;
      rewrite (instantiate_fields_arity _ _ _ _ Hnext); exact Hvalid|].
    apply incl_remove. eapply IH; eauto.
Qed.

Lemma instantiate_header_freevars : forall header schema fields value values body result,
  match_arity body=true -> instantiate_bytes_header header schema fields value values body=OK result ->
  incl (free_variables result) (remove_pattern_variables (Pbytes header schema fields) (free_variables body)).
Proof.
  intros * Hvalid H. unfold instantiate_bytes_header in H.
  destruct (instantiate_field_values fields values body) as [next|error] eqn:Hnext; try discriminate.
  inversion H; subst. unfold remove_pattern_variables; simpl.
  eapply incl_tran; [apply arity_value_substitution_removes_variable;
    rewrite (instantiate_fields_arity _ _ _ _ Hnext); exact Hvalid|].
  apply incl_remove. eapply instantiate_fields_freevars; eauto.
Qed.

Theorem execute_packet_match_freevars : forall env m descriptor offset sid header rest fields yes no final result,
  match_arity yes=true -> match_arity no=true ->
  execute_packet_match env m descriptor offset sid header rest fields yes no=OK(final,result) ->
  incl (free_variables result)
    (remove_pattern_variables (Pbytes header (Stype sid Ctypes.noattr) fields) (free_variables yes) ++
     remove_pattern_variables (Pbytes rest Bytes []) (free_variables no)).
Proof.
  intros * Hyes Hno Hexec. unfold execute_packet_match in Hexec.
  destruct (PTree.get sid env) as [co|] eqn:Hco; try discriminate.
  destruct (read_packet_header m descriptor offset (co_sizeof co)) as [outcome|] eqn:Hread; try discriminate.
  destruct outcome as [view bytes|view].
  - destruct (prepare_packet_header (bcomposite_composite_env env) (co_members co) m bytes) as [[prepared block]|error] eqn:Hprepare; try discriminate.
    destruct (read_packet_fields (bcomposite_composite_env env) (bmembers_cmembers (co_members co)) prepared block fields) as [values|error] eqn:Hvalues; try discriminate.
    destruct (instantiate_bytes_header header (Stype sid Ctypes.noattr) fields (Vloc block Ptrofs.zero) values yes) as [body|error] eqn:Hbody; try discriminate.
    inversion Hexec; subst. eapply incl_tran; [exact (instantiate_header_freevars header (Stype sid Ctypes.noattr) fields (Vloc block Ptrofs.zero) values yes result Hyes Hbody)|]. apply incl_appl; apply incl_refl.
  - inversion Hexec; subst. eapply incl_tran; [apply arity_value_substitution_removes_variable; exact Hno|].
    apply incl_appr; apply incl_refl.
Qed.
Print Assumptions execute_packet_match_freevars.
