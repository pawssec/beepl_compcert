(* Regression for binder-aware Match free variables. Before the repair, this
   typed Bind step changed its raw free-variable list from [] to [1]. *)
Require Import List ZArith Integers AST Maps Ctypes Memory.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem BeePL_substitution_proofs.
Import ListNotations.

Definition shadow_pointer := Ptrtype (Reftype (Bprim (Tint I32 Signed noattr)) noattr).
Definition shadow_match := Match (Enone (Ptrtype (Otype (Reftype (Bprim (Tint I32 Signed noattr)) noattr))))
  [Pnone; Psome 1%positive]
  [Unit Utype; Bind 2%positive shadow_pointer (Var 1%positive shadow_pointer) (Unit Utype) Utype] Utype.
Definition shadow_bound := Bind 1%positive Utype (Val Vunit Utype) shadow_match Utype.

Lemma shadow_match_typed : forall env Gamma Sigma,
  type_expr env Gamma Sigma shadow_match nil Utype.
Proof.
  intros. unfold shadow_match.
  eapply ty_matcho with (ef:=[]) (efb:=[]) (branch_effect:=fun _=>[]).
  - apply ty_none; reflexivity.
  - exists 1%positive; left; reflexivity.
  - repeat constructor.
  - reflexivity.
  - intros n pat branch Hp Hb. destruct n as [|[|n]]; simpl in Hp, Hb; try discriminate; try (destruct n; discriminate);
      inversion Hp; inversion Hb; subst.
    + constructor.
    + eapply ty_bind with (ef:=[]) (ef':=[]); [|constructor]. constructor. simpl. apply PTree.gss.
  - intros; reflexivity.
Qed.

Theorem shadow_bound_typed : forall env Gamma Sigma,
  type_expr env Gamma Sigma shadow_bound nil Utype.
Proof. intros. unfold shadow_bound. eapply ty_bind with (ef:=[]) (ef':=[]); [constructor|apply shadow_match_typed]. Qed.

Theorem shadow_bound_actual_step : forall ge p vm m,
  ssem_expr ge p vm m shadow_bound m vm shadow_match.
Proof.
  intros. unfold shadow_bound. change shadow_match with (subst 1%positive (Val Vunit Utype) shadow_match) at 2.
  apply ssem_bind2. apply substitution_function_relation.
Qed.

Example shadow_bound_free_variables : free_variables shadow_bound = [].
Proof. reflexivity. Qed.
Example shadow_match_free_variables : free_variables shadow_match = [].
Proof. reflexivity. Qed.
Theorem shadow_step_preserves_free_variables :
  incl (free_variables shadow_match) (free_variables shadow_bound).
Proof. simpl. intros x H; contradiction. Qed.
