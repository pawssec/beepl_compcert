(* Direct internal function names resolve to code addresses, not scalar
   memory loads. Address authenticity is supplied by the global environment. *)
Require Import List AST Integers Maps Memory Ctypes Globalenvs.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.

Lemma function_full_deref_impossible : forall args effects result variadic m b ofs v,
  ~ deref_addr (Ftype args effects result variadic) m b ofs Full v.
Proof.
  intros args effects result variadic m b ofs v Hread.
  inversion Hread; subst; discriminate.
Qed.

Theorem global_function_variable_progress :
  forall (bge : genv) p vm m x b fn args effects result variadic,
  PTree.get x vm = None ->
  Genv.find_symbol bge x = Some b ->
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  type_of_function fn = Ftype args effects result variadic ->
  ssem_expr bge p vm m (Var x (Ftype args effects result variadic)) m vm
    (Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic)).
Proof. intros. eapply ssem_global_function; eauto. Qed.

Lemma global_function_variable_step_exact :
  forall (bge : genv) p vm m x b args effects result variadic m' vm' e',
  PTree.get x vm = None -> Genv.find_symbol bge x = Some b ->
  ssem_expr bge p vm m (Var x (Ftype args effects result variadic)) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic).
Proof.
  intros bge p vm m x b args effects result variadic m' vm' e' Hmissing Hsymbol Hstep.
  inversion Hstep; subst;
    try solve [exfalso; eapply function_full_deref_impossible; eauto].
  all: repeat split; congruence.
Qed.

Theorem global_function_variable_preservation :
  forall (bge : genv) cenv Gamma Sigma p vm m x b fn args effects result variadic m' vm' e',
  PTree.get x vm = None ->
  Genv.find_symbol bge x = Some b ->
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  type_of_function fn = Ftype args effects result variadic ->
  ssem_expr bge p vm m (Var x (Ftype args effects result variadic)) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic) /\
    type_expr cenv Gamma Sigma e' nil (Ftype args effects result variadic) /\
    Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn).
Proof.
  intros bge cenv Gamma Sigma p vm m x b fn args effects result variadic m' vm' e'
    Hmissing Hsymbol Hfunction Hsignature Hstep.
  destruct (global_function_variable_step_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Hmissing Hsymbol Hstep)
    as [Hm [Hvm He]]. subst m' vm' e'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply ty_valfun|exact Hfunction].
Qed.

Print Assumptions global_function_variable_progress.
Print Assumptions global_function_variable_preservation.


Lemma local_function_variable_step_exact :
  forall (bge : genv) p vm m x b args effects result variadic m' vm' e',
  PTree.get x vm = Some (b, Ftype args effects result variadic) ->
  ssem_expr bge p vm m (Var x (Ftype args effects result variadic)) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic).
Proof.
  intros bge p vm m x b args effects result variadic m' vm' e' Hlocal Hstep.
  inversion Hstep; subst;
    try solve [exfalso; eapply function_full_deref_impossible; eauto].
  all: repeat split; congruence.
Qed.

Theorem local_function_variable_progress :
  forall (bge : genv) p vm m x b fn args effects result variadic,
  PTree.get x vm = Some (b, Ftype args effects result variadic) ->
  Genv.find_funct bge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
  type_of_function fn = Ftype args effects result variadic ->
  ssem_expr bge p vm m (Var x (Ftype args effects result variadic)) m vm
    (Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic)).
Proof. intros. eapply ssem_local_function; eauto. Qed.
