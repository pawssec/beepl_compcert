(* Operator soundness repairs. Import definitions, not admitted BeePL proofs. *)
Require Import List ZArith Integers AST Maps Memory Ctypes Cop Errors.
Require Import BeeTypes BeePL_values BeePL BeePL_sem BeePL_typesystem.

Lemma boolean_result_has_boolean_type : forall cv v,
  decode_boolean_result cv = OK v ->
  forall cenv Gamma Sigma,
  type_expr cenv Gamma Sigma (Val v (Vtype Tbool)) nil (Vtype Tbool).
Proof.
  intros cv v H cenv Gamma Sigma.
  destruct cv; simpl in H; try discriminate.
  inversion H; subst. constructor.
Qed.

Lemma notbool_value_progress_preservation : forall bge p vm m b cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Uop Cop.Onotbool) (Val (Vbool b) (Vtype Tbool) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (negb b)) (Vtype Tbool)) /\
  type_expr cenv Gamma Sigma (Val (Vbool (negb b)) (Vtype Tbool)) nil (Vtype Tbool).
Proof.
  intros. split; [|constructor].
  destruct b; eapply ssem_uop2; reflexivity.
Qed.

Lemma bool_eq_value_progress_preservation : forall bge p vm m b1 b2 cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oeq) (Val (Vbool b1) (Vtype Tbool) :: Val (Vbool b2) (Vtype Tbool) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (Bool.eqb b1 b2)) (Vtype Tbool)) /\
  type_expr cenv Gamma Sigma (Val (Vbool (Bool.eqb b1 b2)) (Vtype Tbool)) nil (Vtype Tbool).
Proof. intros; split; constructor. Qed.

Lemma bool_ne_value_progress_preservation : forall bge p vm m b1 b2 cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop Cop.One) (Val (Vbool b1) (Vtype Tbool) :: Val (Vbool b2) (Vtype Tbool) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (negb (Bool.eqb b1 b2))) (Vtype Tbool)) /\
  type_expr cenv Gamma Sigma (Val (Vbool (negb (Bool.eqb b1 b2))) (Vtype Tbool)) nil (Vtype Tbool).
Proof. intros; split; constructor. Qed.

Lemma int32_eq_value_progress : forall bge p vm m i j,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oeq)
      (Val (Vint i) (Vtype (Tint I32 Signed noattr)) ::
       Val (Vint j) (Vtype (Tint I32 Signed noattr)) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (Int.eq i j)) (Vtype Tbool)).
Proof.
  intros.
  eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
    (ct := Ctypes.Tint I32 Signed noattr) (s := Signed).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (Int.eq i j); reflexivity.
Qed.

Print Assumptions boolean_result_has_boolean_type.
Print Assumptions notbool_value_progress_preservation.
Print Assumptions bool_eq_value_progress_preservation.
Print Assumptions bool_ne_value_progress_preservation.
Print Assumptions int32_eq_value_progress.

Definition comparison_operator (c : comparison) : Cop.binary_operation :=
  match c with
  | Ceq => Cop.Oeq | Cne => Cop.One | Clt => Cop.Olt
  | Cgt => Cop.Ogt | Cle => Cop.Ole | Cge => Cop.Oge
  end.

Lemma decode_boolean_of_bool : forall b,
  decode_boolean_result (Values.Val.of_bool b) = OK (Vbool b).
Proof. destruct b; reflexivity. Qed.

Lemma int32_comparison_value_progress : forall bge p vm m i j c s a,
  ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c))
      (Val (Vint i) (Vtype (Tint I32 s a)) ::
       Val (Vint j) (Vtype (Tint I32 s a)) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (match s with
      | Signed => Int.cmp c i j | Unsigned => Int.cmpu c i j end)) (Vtype Tbool)).
Proof.
  intros. destruct c, s;
  eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite);
    try reflexivity.
  all: simpl; apply decode_boolean_of_bool.
Qed.

Lemma int64_comparison_value_progress : forall bge p vm m i j c s a,
  ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c))
      (Val (Vint64 i) (Vtype (Tlong s a)) ::
       Val (Vint64 j) (Vtype (Tlong s a)) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (match s with
      | Signed => Int64.cmp c i j | Unsigned => Int64.cmpu c i j end)) (Vtype Tbool)).
Proof.
  intros. destruct c, s;
  eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite);
    try reflexivity.
  all: simpl; apply decode_boolean_of_bool.
Qed.

Print Assumptions int32_comparison_value_progress.
Print Assumptions int64_comparison_value_progress.

Require Import BeePL_soundness_memory.

(* Preservation quantifies over every allowed successor, not just the witness
   chosen by a progress proof. Values cannot take evaluation-context steps. *)
Lemma comparison_value_preservation :
  forall c bge p vm m v1 v2 t m' vm' e' cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c))
      (Val v1 t :: Val v2 t :: nil) (Vtype Tbool)) m' vm' e' ->
  m' = m /\ vm' = vm /\
  type_expr cenv Gamma Sigma e' nil (Vtype Tbool).
Proof.
  intros c bge p vm m v1 v2 t m' vm' e' cenv Gamma Sigma Hstep.
  destruct c; inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto];
    try discriminate;
    repeat split; auto; try solve [constructor];
    eapply boolean_result_has_boolean_type; eauto.
Qed.

Lemma notbool_value_preservation :
  forall bge p vm m b m' vm' e' cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Uop Cop.Onotbool) (Val (Vbool b) (Vtype Tbool) :: nil) (Vtype Tbool))
    m' vm' e' ->
  m' = m /\ vm' = vm /\
  type_expr cenv Gamma Sigma e' nil (Vtype Tbool).
Proof.
  intros bge p vm m b m' vm' e' cenv Gamma Sigma Hstep.
  inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  repeat split; auto. eapply boolean_result_has_boolean_type; eauto.
Qed.

Print Assumptions comparison_value_preservation.
Print Assumptions notbool_value_preservation.

Lemma int32_shl_value_progress : forall bge p vm m i j s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oshl)
      (Val (Vint i) (Vtype (Tint I32 s a)) ::
       Val (Vint j) (Vtype (Tint I32 s a)) :: nil) (Vtype (Tint I32 s a)))
    m vm (Val v (Vtype (Tint I32 s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tint I32 s a))) nil (Vtype (Tint I32 s a)).
Proof.
  intros. destruct (Int.ltu j Int.iwordsize) eqn:Hcount.
  - exists (Vint (Int.shl i j)). split; [|constructor].
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (ct := Ctypes.Tint I32 s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + destruct s; cbv beta iota zeta delta [Cop.sem_binary_operation Cop.sem_shl Cop.sem_shr Cop.sem_shift Cop.classify_shift Ctypes.typeconv trans_bvalue_cvalue]; rewrite Hcount; reflexivity.
    + reflexivity.
  - exists (Vint Int.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (ct := Ctypes.Tint I32 s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + reflexivity.
Qed.

Lemma int32_shr_value_progress : forall bge p vm m i j s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oshr)
      (Val (Vint i) (Vtype (Tint I32 s a)) ::
       Val (Vint j) (Vtype (Tint I32 s a)) :: nil) (Vtype (Tint I32 s a)))
    m vm (Val v (Vtype (Tint I32 s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tint I32 s a))) nil (Vtype (Tint I32 s a)).
Proof.
  intros. destruct (Int.ltu j Int.iwordsize) eqn:Hcount.
  - exists (Vint (match s with Signed => Int.shr i j | Unsigned => Int.shru i j end)).
    split; [|constructor].
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (ct := Ctypes.Tint I32 s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + destruct s; cbv beta iota zeta delta [Cop.sem_binary_operation Cop.sem_shl Cop.sem_shr Cop.sem_shift Cop.classify_shift Ctypes.typeconv trans_bvalue_cvalue]; rewrite Hcount; reflexivity.
    + destruct s; reflexivity.
  - exists (Vint Int.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (ct := Ctypes.Tint I32 s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + reflexivity.
Qed.

Print Assumptions int32_shl_value_progress.
Print Assumptions int32_shr_value_progress.

Lemma int64_shl_value_progress : forall bge p vm m i j s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oshl)
      (Val (Vint64 i) (Vtype (Tlong s a)) ::
       Val (Vint64 j) (Vtype (Tlong s a)) :: nil) (Vtype (Tlong s a)))
    m vm (Val v (Vtype (Tlong s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tlong s a))) nil (Vtype (Tlong s a)).
Proof.
  intros. destruct (Int64.ltu j Int64.iwordsize) eqn:Hcount.
  - exists (Vint64 (Int64.shl i j)). split; [|constructor].
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (ct := Ctypes.Tlong s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + destruct s; cbv beta iota zeta delta [Cop.sem_binary_operation Cop.sem_shl Cop.sem_shr Cop.sem_shift Cop.classify_shift Ctypes.typeconv trans_bvalue_cvalue]; rewrite Hcount; reflexivity.
    + reflexivity.
  - exists (Vint64 Int64.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (ct := Ctypes.Tlong s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + reflexivity.
Qed.

Lemma int64_shr_value_progress : forall bge p vm m i j s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop Cop.Oshr)
      (Val (Vint64 i) (Vtype (Tlong s a)) ::
       Val (Vint64 j) (Vtype (Tlong s a)) :: nil) (Vtype (Tlong s a)))
    m vm (Val v (Vtype (Tlong s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tlong s a))) nil (Vtype (Tlong s a)).
Proof.
  intros. destruct (Int64.ltu j Int64.iwordsize) eqn:Hcount.
  - exists (Vint64 (match s with Signed => Int64.shr i j | Unsigned => Int64.shru i j end)).
    split; [|constructor].
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (ct := Ctypes.Tlong s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + destruct s; cbv beta iota zeta delta [Cop.sem_binary_operation Cop.sem_shl Cop.sem_shr Cop.sem_shift Cop.classify_shift Ctypes.typeconv trans_bvalue_cvalue]; rewrite Hcount; reflexivity.
    + destruct s; reflexivity.
  - exists (Vint64 Int64.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (ct := Ctypes.Tlong s a) (s := s).
    + reflexivity.
    + reflexivity.
    + cbn [check_unsafe_op is_val_shift]. rewrite Hcount. reflexivity.
    + reflexivity.
Qed.

Print Assumptions int64_shl_value_progress.
Print Assumptions int64_shr_value_progress.

(* Total integer arithmetic/bitwise operators; division and shifts have separate
   guarded cases. This classification is proof-side only. *)
Inductive total_integer_operator :=
| IntegerAdd | IntegerSub | IntegerMul | IntegerAnd | IntegerOr | IntegerXor.

Definition integer_operator (op : total_integer_operator) : Cop.binary_operation :=
  match op with
  | IntegerAdd => Cop.Oadd | IntegerSub => Cop.Osub | IntegerMul => Cop.Omul
  | IntegerAnd => Cop.Oand | IntegerOr => Cop.Oor | IntegerXor => Cop.Oxor
  end.

Definition integer32_result (op : total_integer_operator) (i j : Int.int) : Int.int :=
  match op with
  | IntegerAdd => Int.add i j | IntegerSub => Int.sub i j | IntegerMul => Int.mul i j
  | IntegerAnd => Int.and i j | IntegerOr => Int.or i j | IntegerXor => Int.xor i j
  end.

Definition integer64_result (op : total_integer_operator) (i j : Int64.int) : Int64.int :=
  match op with
  | IntegerAdd => Int64.add i j | IntegerSub => Int64.sub i j | IntegerMul => Int64.mul i j
  | IntegerAnd => Int64.and i j | IntegerOr => Int64.or i j | IntegerXor => Int64.xor i j
  end.

Lemma total_integer_operator_safe : forall op s v1 v2,
  check_unsafe_op (integer_operator op) s v1 v2 = false.
Proof. destruct op; reflexivity. Qed.

Lemma total_integer_operator_result_type : forall op ty,
  binary_result_type (integer_operator op) ty = ty.
Proof. destruct op; reflexivity. Qed.

Lemma total_integer32_operation : forall op cenv m sz s a i j,
  sem_binary_operation cenv (integer_operator op)
    (Values.Vint i) (Ctypes.Tint sz s a) (Values.Vint j) (Ctypes.Tint sz s a) m =
  Some (Values.Vint (integer32_result op i j)).
Proof. intros; destruct op, sz, s; reflexivity. Qed.

Lemma total_integer64_operation : forall op cenv m s a i j,
  sem_binary_operation cenv (integer_operator op)
    (Values.Vlong i) (Ctypes.Tlong s a) (Values.Vlong j) (Ctypes.Tlong s a) m =
  Some (Values.Vlong (integer64_result op i j)).
Proof. intros; destruct op, s; reflexivity. Qed.

Lemma total_integer32_decode : forall op i,
  decode_binary_result (integer_operator op) (Values.Vint i) = OK (Vint i).
Proof. destruct op; reflexivity. Qed.

Lemma total_integer64_decode : forall op i,
  decode_binary_result (integer_operator op) (Values.Vlong i) = OK (Vint64 i).
Proof. destruct op; reflexivity. Qed.

Theorem total_integer32_value_progress : forall op bge p vm m i j sz s a cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a)))
    m vm (Val (Vint (integer32_result op i j)) (Vtype (Tint sz s a))) /\
  type_expr cenv Gamma Sigma (Val (Vint (integer32_result op i j)) (Vtype (Tint sz s a)))
    nil (Vtype (Tint sz s a)).
Proof.
  intros. split; [|constructor]. destruct op;
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite); try reflexivity.
  all: destruct sz, s; reflexivity.
Qed.

Theorem total_integer64_value_progress : forall op bge p vm m i j s a cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a)))
    m vm (Val (Vint64 (integer64_result op i j)) (Vtype (Tlong s a))) /\
  type_expr cenv Gamma Sigma (Val (Vint64 (integer64_result op i j)) (Vtype (Tlong s a)))
    nil (Vtype (Tlong s a)).
Proof.
  intros. split; [|constructor]. destruct op;
    eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite); try reflexivity.
  all: destruct s; reflexivity.
Qed.

Print Assumptions total_integer32_value_progress.
Print Assumptions total_integer64_value_progress.

Theorem total_integer32_value_step_result :
  forall op bge p vm m i j sz s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint (integer32_result op i j)) (Vtype (Tint sz s a)).
Proof.
  intros op bge p vm m i j sz s a m' vm' e' Hstep.
  inversion Hstep; subst;
    repeat rewrite total_integer_operator_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  - match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ =>
      rewrite total_integer_operator_safe in Hbad; discriminate
    end.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite total_integer32_operation in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite total_integer32_decode in Hdecode; inversion Hdecode; subst
    end.
    repeat split; reflexivity.
Qed.

Theorem total_integer64_value_step_result :
  forall op bge p vm m i j s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint64 (integer64_result op i j)) (Vtype (Tlong s a)).
Proof.
  intros op bge p vm m i j s a m' vm' e' Hstep.
  inversion Hstep; subst;
    repeat rewrite total_integer_operator_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  - match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ =>
      rewrite total_integer_operator_safe in Hbad; discriminate
    end.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite total_integer64_operation in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite total_integer64_decode in Hdecode; inversion Hdecode; subst
    end.
    repeat split; reflexivity.
Qed.

Print Assumptions total_integer32_value_step_result.
Print Assumptions total_integer64_value_step_result.

Definition division_operator (remainder : bool) : Cop.binary_operation :=
  if remainder then Cop.Omod else Cop.Odiv.

Definition division32_result (remainder : bool) (s : signedness) (i j : Int.int) : Int.int :=
  match remainder, s with
  | false, Signed => Int.divs i j | false, Unsigned => Int.divu i j
  | true, Signed => Int.mods i j | true, Unsigned => Int.modu i j
  end.

Definition division64_result (remainder : bool) (s : signedness) (i j : Int64.int) : Int64.int :=
  match remainder, s with
  | false, Signed => Int64.divs i j | false, Unsigned => Int64.divu i j
  | true, Signed => Int64.mods i j | true, Unsigned => Int64.modu i j
  end.

Lemma division32_operation : forall remainder cenv m s a i j,
  sem_binary_operation cenv (division_operator remainder)
    (Values.Vint i) (Ctypes.Tint I32 s a) (Values.Vint j) (Ctypes.Tint I32 s a) m =
  if check_unsafe_op (division_operator remainder) s (Vint i) (Vint j)
  then None else Some (Values.Vint (division32_result remainder s i j)).
Proof.
  intros. destruct remainder, s;
    cbv beta iota zeta delta [division_operator division32_result sem_binary_operation sem_mod sem_div sem_binarith
      classify_binarith binarith_type sem_cast classify_cast cast_int_int Archi.ptr64
      check_unsafe_op is_zero_val is_overflow_vals];
    destruct (Int.eq j Int.zero); destruct (Int.eq i (Int.repr Int.min_signed));
    destruct (Int.eq j Int.mone); reflexivity.
Qed.

Lemma division64_operation : forall remainder cenv m s a i j,
  sem_binary_operation cenv (division_operator remainder)
    (Values.Vlong i) (Ctypes.Tlong s a) (Values.Vlong j) (Ctypes.Tlong s a) m =
  if check_unsafe_op (division_operator remainder) s (Vint64 i) (Vint64 j)
  then None else Some (Values.Vlong (division64_result remainder s i j)).
Proof.
  intros. destruct remainder, s;
    cbv beta iota zeta delta [division_operator division64_result sem_binary_operation sem_mod sem_div sem_binarith
      classify_binarith binarith_type sem_cast classify_cast cast_int_int Archi.ptr64
      check_unsafe_op is_zero_val is_overflow_vals];
    destruct (Int64.eq j Int64.zero); destruct (Int64.eq i (Int64.repr Int64.min_signed));
    destruct (Int64.eq j Int64.mone); reflexivity.
Qed.

Definition guarded_division32_result remainder s i j :=
  if check_unsafe_op (division_operator remainder) s (Vint i) (Vint j)
  then Int.zero else division32_result remainder s i j.

Definition guarded_division64_result remainder s i j :=
  if check_unsafe_op (division_operator remainder) s (Vint64 i) (Vint64 j)
  then Int64.zero else division64_result remainder s i j.

Theorem division32_value_progress : forall remainder bge p vm m i j s a cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint i) (Vtype (Tint I32 s a)) :: Val (Vint j) (Vtype (Tint I32 s a)) :: nil)
      (Vtype (Tint I32 s a)))
    m vm (Val (Vint (guarded_division32_result remainder s i j)) (Vtype (Tint I32 s a))) /\
  type_expr cenv Gamma Sigma
    (Val (Vint (guarded_division32_result remainder s i j)) (Vtype (Tint I32 s a)))
    nil (Vtype (Tint I32 s a)).
Proof.
  intros. split; [|constructor]. unfold guarded_division32_result.
  destruct (check_unsafe_op (division_operator remainder) s (Vint i) (Vint j)) eqn:Hbad.
  - eapply ssem_bop3_unsafe; [reflexivity | reflexivity | exact Hbad | reflexivity].
  - assert (Hoperation : sem_binary_operation (PTree.empty Ctypes.composite) (division_operator remainder)
      (Values.Vint i) (Ctypes.Tint I32 s a) (Values.Vint j) (Ctypes.Tint I32 s a) m =
      Some (Values.Vint (division32_result remainder s i j))).
    { rewrite division32_operation, Hbad. reflexivity. }
    destruct remainder; eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite) (s := s);
      eauto; reflexivity.
Qed.

Theorem division64_value_progress : forall remainder bge p vm m i j s a cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a)))
    m vm (Val (Vint64 (guarded_division64_result remainder s i j)) (Vtype (Tlong s a))) /\
  type_expr cenv Gamma Sigma
    (Val (Vint64 (guarded_division64_result remainder s i j)) (Vtype (Tlong s a)))
    nil (Vtype (Tlong s a)).
Proof.
  intros. split; [|constructor]. unfold guarded_division64_result.
  destruct (check_unsafe_op (division_operator remainder) s (Vint64 i) (Vint64 j)) eqn:Hbad.
  - eapply ssem_bop3_unsafe; [reflexivity | reflexivity | exact Hbad | reflexivity].
  - assert (Hoperation : sem_binary_operation (PTree.empty Ctypes.composite) (division_operator remainder)
      (Values.Vlong i) (Ctypes.Tlong s a) (Values.Vlong j) (Ctypes.Tlong s a) m =
      Some (Values.Vlong (division64_result remainder s i j))).
    { rewrite division64_operation, Hbad. reflexivity. }
    destruct remainder; eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite) (s := s);
      eauto; reflexivity.
Qed.

Print Assumptions division32_value_progress.
Print Assumptions division64_value_progress.

Lemma division_result_type : forall remainder ty,
  binary_result_type (division_operator remainder) ty = ty.
Proof. destruct remainder; reflexivity. Qed.

Lemma division32_decode : forall remainder i,
  decode_binary_result (division_operator remainder) (Values.Vint i) = OK (Vint i).
Proof. destruct remainder; reflexivity. Qed.

Lemma division64_decode : forall remainder i,
  decode_binary_result (division_operator remainder) (Values.Vlong i) = OK (Vint64 i).
Proof. destruct remainder; reflexivity. Qed.

Theorem division32_value_step_result :
  forall remainder bge p vm m i j s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint i) (Vtype (Tint I32 s a)) :: Val (Vint j) (Vtype (Tint I32 s a)) :: nil)
      (Vtype (Tint I32 s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint (guarded_division32_result remainder s i j)) (Vtype (Tint I32 s a)).
Proof.
  intros remainder bge p vm m i j s a m' vm' e' Hstep.
  inversion Hstep; subst; repeat rewrite division_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: match goal with Hsign : arithmetic_signedness_of_type _ = Some _ |- _ =>
    cbn [arithmetic_signedness_of_type promoted_integer_signedness signedness_of_type signedness_of_primitive] in Hsign; inversion Hsign; subst
  end.
  - match goal with Hz : return_bzero _ = OK _ |- _ => inversion Hz; subst end.
    unfold guarded_division32_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ => rewrite Hbad end.
    repeat split; reflexivity.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _,
      Hbad : check_unsafe_op _ _ _ _ = false |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite division32_operation, Hbad in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite division32_decode in Hdecode; inversion Hdecode; subst
    end.
    unfold guarded_division32_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = false |- _ => rewrite Hbad end.
    repeat split; reflexivity.
Qed.

Theorem division64_value_step_result :
  forall remainder bge p vm m i j s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint64 (guarded_division64_result remainder s i j)) (Vtype (Tlong s a)).
Proof.
  intros remainder bge p vm m i j s a m' vm' e' Hstep.
  inversion Hstep; subst; repeat rewrite division_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: match goal with Hsign : arithmetic_signedness_of_type _ = Some _ |- _ =>
    cbn [arithmetic_signedness_of_type promoted_integer_signedness signedness_of_type signedness_of_primitive] in Hsign; inversion Hsign; subst
  end.
  - match goal with Hz : return_bzero _ = OK _ |- _ => inversion Hz; subst end.
    unfold guarded_division64_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ => rewrite Hbad end.
    repeat split; reflexivity.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _,
      Hbad : check_unsafe_op _ _ _ _ = false |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite division64_operation, Hbad in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite division64_decode in Hdecode; inversion Hdecode; subst
    end.
    unfold guarded_division64_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = false |- _ => rewrite Hbad end.
    repeat split; reflexivity.
Qed.

Print Assumptions division32_value_step_result.
Print Assumptions division64_value_step_result.

Lemma promoted_integer_division_operation : forall remainder cenv m sz s a i j,
  sem_binary_operation cenv (division_operator remainder)
    (Values.Vint i) (Ctypes.Tint sz s a) (Values.Vint j) (Ctypes.Tint sz s a) m =
  if check_unsafe_op (division_operator remainder) (promoted_integer_signedness sz s) (Vint i) (Vint j)
  then None else Some (Values.Vint (division32_result remainder (promoted_integer_signedness sz s) i j)).
Proof.
  intros. destruct remainder, sz, s;
    cbv beta iota zeta delta [division_operator division32_result sem_binary_operation sem_mod sem_div sem_binarith
      classify_binarith binarith_type sem_cast classify_cast cast_int_int Archi.ptr64
      promoted_integer_signedness check_unsafe_op is_zero_val is_overflow_vals];
    destruct (Int.eq j Int.zero); destruct (Int.eq i (Int.repr Int.min_signed));
    destruct (Int.eq j Int.mone); reflexivity.
Qed.

Theorem guarded_integer_division_semantics : forall remainder cenv m ty first last s,
  (is_primint ty || is_primlong ty)%bool = true ->
  arithmetic_signedness_of_type ty = Some s ->
  typeof_value first ty -> typeof_value last ty ->
  check_unsafe_op (division_operator remainder) s first last = false ->
  exists cv v,
    sem_binary_operation cenv (division_operator remainder)
      (trans_bvalue_cvalue first) (transBeePL_type ty)
      (trans_bvalue_cvalue last) (transBeePL_type ty) m = Some cv /\
    cv <> Values.Vundef /\ trans_cvalue_bvalue cv = OK v.
Proof.
  intros remainder cenv m ty first last s Hnumeric Hsign Hfirst Hlast Hsafe.
  destruct ty; simpl in Hnumeric; try discriminate.
  destruct p as [|sz sg attr|sg attr]; simpl in Hnumeric; try discriminate;
    destruct first as [|b1|i1|l1|block1 ofs1|o1];
    destruct last as [|b2|i2|l2|block2 ofs2|o2];
    simpl in Hfirst, Hlast; try contradiction.
  all: cbn [arithmetic_signedness_of_type signedness_of_type signedness_of_primitive] in Hsign;
    inversion Hsign; subst s.
  - exists (Values.Vint (division32_result remainder (promoted_integer_signedness sz sg) i1 i2)),
      (Vint (division32_result remainder (promoted_integer_signedness sz sg) i1 i2)).
    split.
    + cbn [trans_bvalue_cvalue transBeePL_type]. rewrite promoted_integer_division_operation, Hsafe. reflexivity.
    + split; [discriminate | reflexivity].
  - exists (Values.Vlong (division64_result remainder sg l1 l2)),
      (Vint64 (division64_result remainder sg l1 l2)).
    split.
    + cbn [trans_bvalue_cvalue transBeePL_type]. rewrite division64_operation, Hsafe. reflexivity.
    + split; [discriminate | reflexivity].
Qed.

Theorem promoted_integer_division_progress : forall remainder bge p vm m i j sz s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a))) m vm (Val v (Vtype (Tint sz s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tint sz s a))) nil (Vtype (Tint sz s a)).
Proof.
  intros.
  destruct (check_unsafe_op (division_operator remainder) (promoted_integer_signedness sz s)
    (Vint i) (Vint j)) eqn:Hbad.
  - exists (Vint Int.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (s := promoted_integer_signedness sz s);
      [reflexivity | reflexivity | exact Hbad | reflexivity].
  - exists (Vint (division32_result remainder (promoted_integer_signedness sz s) i j)).
    split; [|constructor].
    assert (Hoperation : sem_binary_operation (PTree.empty Ctypes.composite) (division_operator remainder)
      (Values.Vint i) (Ctypes.Tint sz s a) (Values.Vint j) (Ctypes.Tint sz s a) m =
      Some (Values.Vint (division32_result remainder (promoted_integer_signedness sz s) i j))).
    { rewrite promoted_integer_division_operation, Hbad. reflexivity. }
    destruct remainder; eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (s := promoted_integer_signedness sz s); eauto; reflexivity.
Qed.

Print Assumptions promoted_integer_division_operation.
Print Assumptions guarded_integer_division_semantics.
Print Assumptions promoted_integer_division_progress.

Definition guarded_promoted_division_result remainder sz s i j :=
  if check_unsafe_op (division_operator remainder) (promoted_integer_signedness sz s) (Vint i) (Vint j)
  then Int.zero else division32_result remainder (promoted_integer_signedness sz s) i j.

Theorem promoted_integer_division_step_result :
  forall remainder bge p vm m i j sz s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint (guarded_promoted_division_result remainder sz s i j)) (Vtype (Tint sz s a)).
Proof.
  intros remainder bge p vm m i j sz s a m' vm' e' Hstep.
  inversion Hstep; subst; repeat rewrite division_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: match goal with Hsign : arithmetic_signedness_of_type _ = Some _ |- _ =>
    cbn [arithmetic_signedness_of_type promoted_integer_signedness signedness_of_type signedness_of_primitive] in Hsign; inversion Hsign; subst
  end.
  - match goal with Hz : return_bzero _ = OK _ |- _ => inversion Hz; subst end.
    unfold guarded_promoted_division_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ => rewrite Hbad end.
    repeat split; reflexivity.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _,
      Hbad : check_unsafe_op _ _ _ _ = false |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite promoted_integer_division_operation, Hbad in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite division32_decode in Hdecode; inversion Hdecode; subst
    end.
    unfold guarded_promoted_division_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = false |- _ => rewrite Hbad end.
    repeat split; reflexivity.
Qed.

Print Assumptions promoted_integer_division_step_result.

Lemma typed_numeric_value_pair : forall cenv Gamma Sigma first last ty ef1 ef2,
  (is_primint ty || is_primlong ty)%bool = true ->
  type_expr cenv Gamma Sigma (Val first ty) ef1 ty ->
  type_expr cenv Gamma Sigma (Val last ty) ef2 ty ->
  (exists sz s a i j, ty = Vtype (Tint sz s a) /\ first = Vint i /\ last = Vint j) \/
  (exists s a i j, ty = Vtype (Tlong s a) /\ first = Vint64 i /\ last = Vint64 j).
Proof.
  intros cenv Gamma Sigma first last ty ef1 ef2 Hnumeric Hfirst Hlast.
  pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hfirst) as Hshape1.
  pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hlast) as Hshape2.
  destruct ty; simpl in Hnumeric; try discriminate.
  destruct p; simpl in Hnumeric; try discriminate;
    destruct first; destruct last; simpl in Hshape1, Hshape2; try contradiction.
  - left. do 5 eexists. repeat split; reflexivity.
  - right. do 4 eexists. repeat split; reflexivity.
Qed.

Lemma division_typing_components : forall remainder cenv Gamma Sigma left right ty ef,
  type_expr cenv Gamma Sigma (Prim (Bop (division_operator remainder)) (left :: right :: nil) ty) ef ty ->
  (is_primint ty || is_primlong ty)%bool = true /\
  exists ef1 ef2, ef = ef1 ++ ef2 /\
    type_expr cenv Gamma Sigma left ef1 ty /\ type_expr cenv Gamma Sigma right ef2 ty.
Proof.
  intros remainder cenv Gamma Sigma left right ty ef Htyped.
  destruct remainder; inversion Htyped; subst; split; [assumption | eauto 8 | assumption | eauto 8].
Qed.

Theorem typed_division_value_progress :
  forall remainder bge p cenv Gamma Sigma vm m first last ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (division_operator remainder)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  exists v,
    ssem_expr bge p vm m
      (Prim (Bop (division_operator remainder)) (Val first ty :: Val last ty :: nil) ty)
      m vm (Val v ty) /\ type_expr cenv Gamma Sigma (Val v ty) nil ty.
Proof.
  intros remainder bge p cenv Gamma Sigma vm m first last ty ef Htyped.
  destruct (division_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - apply promoted_integer_division_progress.
  - exists (Vint64 (guarded_division64_result remainder s i j)).
    apply division64_value_progress.
Qed.

Theorem typed_division_value_preservation :
  forall remainder bge p cenv Gamma Sigma vm m first last ty ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Prim (Bop (division_operator remainder)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder)) (Val first ty :: Val last ty :: nil) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros remainder bge p cenv Gamma Sigma vm m first last ty ef vm' m' e' Htyped Hstep.
  destruct (division_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - destruct (promoted_integer_division_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
  - destruct (division64_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
Qed.

Print Assumptions typed_numeric_value_pair.
Print Assumptions typed_division_value_progress.
Print Assumptions typed_division_value_preservation.

Lemma total_integer_typing_components : forall op cenv Gamma Sigma left right ty ef,
  type_expr cenv Gamma Sigma (Prim (Bop (integer_operator op)) (left :: right :: nil) ty) ef ty ->
  (is_primint ty || is_primlong ty)%bool = true /\
  exists ef1 ef2, ef = ef1 ++ ef2 /\
    type_expr cenv Gamma Sigma left ef1 ty /\ type_expr cenv Gamma Sigma right ef2 ty.
Proof.
  intros op cenv Gamma Sigma left right ty ef Htyped.
  destruct op; inversion Htyped; subst; split; try assumption; eauto 8.
Qed.

Theorem typed_total_integer_value_progress :
  forall op bge p cenv Gamma Sigma vm m first last ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (integer_operator op)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  exists v,
    ssem_expr bge p vm m
      (Prim (Bop (integer_operator op)) (Val first ty :: Val last ty :: nil) ty)
      m vm (Val v ty) /\ type_expr cenv Gamma Sigma (Val v ty) nil ty.
Proof.
  intros op bge p cenv Gamma Sigma vm m first last ty ef Htyped.
  destruct (total_integer_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - exists (Vint (integer32_result op i j)). apply total_integer32_value_progress.
  - exists (Vint64 (integer64_result op i j)). apply total_integer64_value_progress.
Qed.

Theorem typed_total_integer_value_preservation :
  forall op bge p cenv Gamma Sigma vm m first last ty ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Prim (Bop (integer_operator op)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op)) (Val first ty :: Val last ty :: nil) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros op bge p cenv Gamma Sigma vm m first last ty ef vm' m' e' Htyped Hstep.
  destruct (total_integer_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - destruct (total_integer32_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
  - destruct (total_integer64_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
Qed.

Print Assumptions typed_total_integer_value_progress.
Print Assumptions typed_total_integer_value_preservation.

(* Evaluation-context progress: the premises are the two expression induction
   hypotheses and the already proved value-operation case. *)
Lemma binary_progress_from_operands :
  forall bop bge p cenv Gamma Sigma vm m left right ty rt ef1 ef2,
  type_expr cenv Gamma Sigma left ef1 ty ->
  type_expr cenv Gamma Sigma right ef2 ty ->
  ((exists v annotation, left = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m left m' vm' e') ->
  ((exists v annotation, right = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m right m' vm' e') ->
  (forall first last, left = Val first ty -> right = Val last ty ->
    exists m' vm' e', ssem_expr bge p vm m
      (Prim (Bop bop) (Val first ty :: Val last ty :: nil) rt) m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m
    (Prim (Bop bop) (left :: right :: nil) rt) m' vm' e'.
Proof.
  intros bop bge p cenv Gamma Sigma vm m left right ty rt ef1 ef2
    Hleft Hright Hprogress_left Hprogress_right Hvalues.
  destruct Hprogress_left as [[first [annotation He]] | [m' [vm' [e' Hstep]]]].
  - subst left. pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Hannotation.
    simpl in Hannotation. subst annotation.
    destruct Hprogress_right as [[last [annotation He]] | [m' [vm' [e' Hstep]]]].
    + subst right. pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as Hannotation.
      simpl in Hannotation. subst annotation. apply Hvalues; reflexivity.
    + do 3 eexists. apply ssem_bop2. exact Hstep.
  - do 3 eexists. apply ssem_bop1. exact Hstep.
Qed.

Theorem division_progress_from_operands :
  forall remainder bge p cenv Gamma Sigma vm m left right ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (division_operator remainder)) (left :: right :: nil) ty) ef ty ->
  ((exists v annotation, left = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m left m' vm' e') ->
  ((exists v annotation, right = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m right m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m
    (Prim (Bop (division_operator remainder)) (left :: right :: nil) ty) m' vm' e'.
Proof.
  intros remainder bge p cenv Gamma Sigma vm m left right ty ef Htyped Hleft Hright.
  destruct (division_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  eapply binary_progress_from_operands; [exact Hfirst | exact Hlast | exact Hleft | exact Hright |].
  intros first last Hone Htwo. subst left right.
  destruct (typed_division_value_progress _ bge p _ _ _ vm m _ _ _ _ Htyped) as [v [Hstep Htype]].
  eauto.
Qed.

Theorem total_integer_progress_from_operands :
  forall op bge p cenv Gamma Sigma vm m left right ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (integer_operator op)) (left :: right :: nil) ty) ef ty ->
  ((exists v annotation, left = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m left m' vm' e') ->
  ((exists v annotation, right = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m right m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m
    (Prim (Bop (integer_operator op)) (left :: right :: nil) ty) m' vm' e'.
Proof.
  intros op bge p cenv Gamma Sigma vm m left right ty ef Htyped Hleft Hright.
  destruct (total_integer_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  eapply binary_progress_from_operands; [exact Hfirst | exact Hlast | exact Hleft | exact Hright |].
  intros first last Hone Htwo. subst left right.
  destruct (typed_total_integer_value_progress _ bge p _ _ _ vm m _ _ _ _ Htyped) as [v [Hstep Htype]].
  eauto.
Qed.

Print Assumptions division_progress_from_operands.
Print Assumptions total_integer_progress_from_operands.

Require Import BeePL_auxlemmas.

Lemma binary_preservation_from_operands :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    bop bge p cenv Gamma Sigma vm m left right ty rt ef1 ef2 vm' m' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma left ef1 ty ->
  type_expr cenv Gamma Sigma right ef2 ty ->
  (forall nextSigma nextLeft nextRight nextEf1 nextEf2,
    type_expr cenv Gamma nextSigma nextLeft nextEf1 ty ->
    type_expr cenv Gamma nextSigma nextRight nextEf2 ty ->
    type_expr cenv Gamma nextSigma
      (Prim (Bop bop) (nextLeft :: nextRight :: nil) rt) (nextEf1 ++ nextEf2) rt) ->
  (forall operand operandEffect,
    (operand = left \/ operand = right) ->
    type_expr cenv Gamma Sigma operand operandEffect ty ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect ty /\
        sub_effect nextEffect operandEffect = true) ->
  (forall first a last b, left = Val first a -> right = Val last b ->
    forall nextM nextVm nextExpr,
      ssem_expr bge p vm m (Prim (Bop bop) (left :: right :: nil) rt) nextM nextVm nextExpr ->
      nextM = m /\ nextVm = vm /\ type_expr cenv Gamma Sigma nextExpr nil rt) ->
  ssem_expr bge p vm m (Prim (Bop bop) (left :: right :: nil) rt) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' rt /\ sub_effect ef' (ef1 ++ ef2) = true.
Proof.
  intros Q bop bge p cenv Gamma Sigma vm m left right ty rt ef1 ef2 vm' m' e'
    Hstate Hleft Hright Hrebuild Hlocal Hvalues Hstep.
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m left _ _ _ |- _ =>
      destruct (Hlocal left ef1 (or_introl eq_refl) Hleft _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, (nextEffect ++ ef2). split; [exact Hext |].
    split; [exact Hstate' |]. split.
    + apply Hrebuild; [exact Htyped' |]. eapply (proj2 typing_store_extension); eauto.
    + apply sub_effect_concat; [exact Hsub | apply sub_effect_refl].
  - match goal with Hs : ssem_expr bge p vm m right _ _ _ |- _ =>
      destruct (Hlocal right ef2 (or_intror eq_refl) Hright _ _ _ Hs)
        as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, (ef1 ++ nextEffect). split; [exact Hext |].
    split; [exact Hstate' |]. split.
    + apply Hrebuild; [|exact Htyped']. eapply (proj2 typing_store_extension); eauto.
    + apply sub_effect_concat; [apply sub_effect_refl | exact Hsub].
  all: destruct (Hvalues _ _ _ _ eq_refl eq_refl _ _ _ Hstep) as [Hm [Hvm Hresult]];
    exists Sigma, nil; split; [apply store_context_extends_refl |];
    split; [exact Hstate |]; split; [exact Hresult | apply sub_effect_nil].
Qed.

Print Assumptions binary_preservation_from_operands.

Theorem division_preservation_from_operands :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma
    (Prim (Bop (division_operator op)) (left :: right :: nil) ty) ef ty ->
  (forall operand operandEffect,
    (operand = left \/ operand = right) ->
    type_expr cenv Gamma Sigma operand operandEffect ty ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect ty /\
        sub_effect nextEffect operandEffect = true) ->
  ssem_expr bge p vm m
    (Prim (Bop (division_operator op)) (left :: right :: nil) ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (division_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hleft Hright]]]]]. subst ef.
  eapply binary_preservation_from_operands;
    [exact Hstate | exact Hleft | exact Hright | | exact Hlocal | | exact Hstep].
  - intros nextSigma nextLeft nextRight nextEf1 nextEf2 Hfirst Hlast.
    destruct op; constructor; assumption.
  - intros first a last b Hone Htwo nextM nextVm nextExpr Hs.
    subst left right.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Ha.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as Hb.
    simpl in Ha, Hb. subst a b.
    eapply typed_division_value_preservation; [exact Htyped | exact Hs].
Qed.

Print Assumptions division_preservation_from_operands.

Theorem total_integer_preservation_from_operands :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma
    (Prim (Bop (integer_operator op)) (left :: right :: nil) ty) ef ty ->
  (forall operand operandEffect,
    (operand = left \/ operand = right) ->
    type_expr cenv Gamma Sigma operand operandEffect ty ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect ty /\
        sub_effect nextEffect operandEffect = true) ->
  ssem_expr bge p vm m
    (Prim (Bop (integer_operator op)) (left :: right :: nil) ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (total_integer_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hleft Hright]]]]]. subst ef.
  eapply binary_preservation_from_operands;
    [exact Hstate | exact Hleft | exact Hright | | exact Hlocal | | exact Hstep].
  - intros nextSigma nextLeft nextRight nextEf1 nextEf2 Hfirst Hlast.
    destruct op; constructor; assumption.
  - intros first a last b Hone Htwo nextM nextVm nextExpr Hs.
    subst left right.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Ha.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as Hb.
    simpl in Ha, Hb. subst a b.
    eapply typed_total_integer_value_preservation; [exact Htyped | exact Hs].
Qed.

Print Assumptions total_integer_preservation_from_operands.

Definition shift_operator (rightshift : bool) := if rightshift then Oshr else Oshl.

Definition shift32_result (rightshift : bool) sz s i j :=
  if rightshift then
    match promoted_integer_signedness sz s with Signed => Int.shr i j | Unsigned => Int.shru i j end
  else Int.shl i j.
Definition shift64_result (rightshift : bool) s i j :=
  if rightshift then match s with Signed => Int64.shr i j | Unsigned => Int64.shru i j end
  else Int64.shl i j.

Lemma shift32_operation : forall rightshift cenv m sz s a i j,
  sem_binary_operation cenv (shift_operator rightshift)
    (Values.Vint i) (Ctypes.Tint sz s a) (Values.Vint j) (Ctypes.Tint sz s a) m =
  if check_unsafe_op (shift_operator rightshift) (promoted_integer_signedness sz s) (Vint i) (Vint j)
  then None else Some (Values.Vint (shift32_result rightshift sz s i j)).
Proof.
  intros. destruct rightshift, sz, s;
    cbv beta iota zeta delta [shift_operator shift32_result promoted_integer_signedness
      sem_binary_operation sem_shl sem_shr sem_shift classify_shift Ctypes.typeconv
      check_unsafe_op is_val_shift];
    destruct (Int.ltu j Int.iwordsize); reflexivity.
Qed.

Lemma shift64_operation : forall rightshift cenv m s a i j,
  sem_binary_operation cenv (shift_operator rightshift)
    (Values.Vlong i) (Ctypes.Tlong s a) (Values.Vlong j) (Ctypes.Tlong s a) m =
  if check_unsafe_op (shift_operator rightshift) s (Vint64 i) (Vint64 j)
  then None else Some (Values.Vlong (shift64_result rightshift s i j)).
Proof.
  intros. destruct rightshift, s;
    cbv beta iota zeta delta [shift_operator shift64_result
      sem_binary_operation sem_shl sem_shr sem_shift classify_shift Ctypes.typeconv
      check_unsafe_op is_val_shift];
    destruct (Int64.ltu j Int64.iwordsize); reflexivity.
Qed.

Lemma shift_result_type : forall rightshift ty,
  binary_result_type (shift_operator rightshift) ty = ty.
Proof. intros; destruct rightshift; reflexivity. Qed.

Lemma shift32_decode : forall rightshift i,
  decode_binary_result (shift_operator rightshift) (Values.Vint i) = OK (Vint i).
Proof. intros; destruct rightshift; reflexivity. Qed.

Lemma shift64_decode : forall rightshift i,
  decode_binary_result (shift_operator rightshift) (Values.Vlong i) = OK (Vint64 i).
Proof. intros; destruct rightshift; reflexivity. Qed.

Print Assumptions shift32_operation.
Print Assumptions shift64_operation.


Definition guarded_shift32_result rightshift sz s i j :=
  if check_unsafe_op (shift_operator rightshift) (promoted_integer_signedness sz s) (Vint i) (Vint j)
  then Int.zero else shift32_result rightshift sz s i j.


Definition guarded_shift64_result rightshift s i j :=
  if check_unsafe_op (shift_operator rightshift) s (Vint64 i) (Vint64 j)
  then Int64.zero else shift64_result rightshift s i j.


Theorem shift32_value_progress : forall rightshift bge p vm m i j sz s a cenv Gamma Sigma,
  exists v,
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a))) m vm (Val v (Vtype (Tint sz s a))) /\
  type_expr cenv Gamma Sigma (Val v (Vtype (Tint sz s a))) nil (Vtype (Tint sz s a)).
Proof.
  intros.
  destruct (check_unsafe_op (shift_operator rightshift) (promoted_integer_signedness sz s)
    (Vint i) (Vint j)) eqn:Hbad.
  - exists (Vint Int.zero). split; [|constructor].
    eapply ssem_bop3_unsafe with (s := promoted_integer_signedness sz s);
      [reflexivity | reflexivity | exact Hbad | reflexivity].
  - exists (Vint (shift32_result rightshift sz s i j)).
    split; [|constructor].
    assert (Hoperation : sem_binary_operation (PTree.empty Ctypes.composite) (shift_operator rightshift)
      (Values.Vint i) (Ctypes.Tint sz s a) (Values.Vint j) (Ctypes.Tint sz s a) m =
      Some (Values.Vint (shift32_result rightshift sz s i j))).
    { rewrite shift32_operation, Hbad. reflexivity. }
    destruct rightshift; eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite)
      (s := promoted_integer_signedness sz s); eauto; reflexivity.
Qed.


Theorem shift64_value_progress : forall rightshift bge p vm m i j s a cenv Gamma Sigma,
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a)))
    m vm (Val (Vint64 (guarded_shift64_result rightshift s i j)) (Vtype (Tlong s a))) /\
  type_expr cenv Gamma Sigma
    (Val (Vint64 (guarded_shift64_result rightshift s i j)) (Vtype (Tlong s a)))
    nil (Vtype (Tlong s a)).
Proof.
  intros. split; [|constructor]. unfold guarded_shift64_result.
  destruct (check_unsafe_op (shift_operator rightshift) s (Vint64 i) (Vint64 j)) eqn:Hbad.
  - eapply ssem_bop3_unsafe; [reflexivity | reflexivity | exact Hbad | reflexivity].
  - assert (Hoperation : sem_binary_operation (PTree.empty Ctypes.composite) (shift_operator rightshift)
      (Values.Vlong i) (Ctypes.Tlong s a) (Values.Vlong j) (Ctypes.Tlong s a) m =
      Some (Values.Vlong (shift64_result rightshift s i j))).
    { rewrite shift64_operation, Hbad. reflexivity. }
    destruct rightshift; eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite) (s := s);
      eauto; reflexivity.
Qed.


Theorem shift32_value_step_result :
  forall rightshift bge p vm m i j sz s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift))
      (Val (Vint i) (Vtype (Tint sz s a)) :: Val (Vint j) (Vtype (Tint sz s a)) :: nil)
      (Vtype (Tint sz s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint (guarded_shift32_result rightshift sz s i j)) (Vtype (Tint sz s a)).
Proof.
  intros rightshift bge p vm m i j sz s a m' vm' e' Hstep.
  inversion Hstep; subst; repeat rewrite shift_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: match goal with Hsign : arithmetic_signedness_of_type _ = Some _ |- _ =>
    cbn [arithmetic_signedness_of_type promoted_integer_signedness signedness_of_type signedness_of_primitive] in Hsign; inversion Hsign; subst
  end.
  - match goal with Hz : return_bzero _ = OK _ |- _ => inversion Hz; subst end.
    unfold guarded_shift32_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ => rewrite Hbad end.
    repeat split; reflexivity.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _,
      Hbad : check_unsafe_op _ _ _ _ = false |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite shift32_operation, Hbad in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite shift32_decode in Hdecode; inversion Hdecode; subst
    end.
    unfold guarded_shift32_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = false |- _ => rewrite Hbad end.
    repeat split; reflexivity.
Qed.


Theorem shift64_value_step_result :
  forall rightshift bge p vm m i j s a m' vm' e',
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift))
      (Val (Vint64 i) (Vtype (Tlong s a)) :: Val (Vint64 j) (Vtype (Tlong s a)) :: nil)
      (Vtype (Tlong s a))) m' vm' e' ->
  m' = m /\ vm' = vm /\
    e' = Val (Vint64 (guarded_shift64_result rightshift s i j)) (Vtype (Tlong s a)).
Proof.
  intros rightshift bge p vm m i j s a m' vm' e' Hstep.
  inversion Hstep; subst; repeat rewrite shift_result_type in *;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  all: match goal with Hsign : arithmetic_signedness_of_type _ = Some _ |- _ =>
    cbn [arithmetic_signedness_of_type promoted_integer_signedness signedness_of_type signedness_of_primitive] in Hsign; inversion Hsign; subst
  end.
  - match goal with Hz : return_bzero _ = OK _ |- _ => inversion Hz; subst end.
    unfold guarded_shift64_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = true |- _ => rewrite Hbad end.
    repeat split; reflexivity.
  - match goal with Hsem : sem_binary_operation _ _ _ _ _ _ _ = Some _,
      Hbad : check_unsafe_op _ _ _ _ = false |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite shift64_operation, Hbad in Hsem; inversion Hsem; subst
    end.
    match goal with Hdecode : decode_binary_result _ _ = OK _ |- _ =>
      rewrite shift64_decode in Hdecode; inversion Hdecode; subst
    end.
    unfold guarded_shift64_result.
    match goal with Hbad : check_unsafe_op _ _ _ _ = false |- _ => rewrite Hbad end.
    repeat split; reflexivity.
Qed.


Lemma shift_typing_components : forall rightshift cenv Gamma Sigma left right ty ef,
  type_expr cenv Gamma Sigma (Prim (Bop (shift_operator rightshift)) (left :: right :: nil) ty) ef ty ->
  (is_primint ty || is_primlong ty)%bool = true /\
  exists ef1 ef2, ef = ef1 ++ ef2 /\
    type_expr cenv Gamma Sigma left ef1 ty /\ type_expr cenv Gamma Sigma right ef2 ty.
Proof.
  intros rightshift cenv Gamma Sigma left right ty ef Htyped.
  destruct rightshift; inversion Htyped; subst; split; [assumption | eauto 8 | assumption | eauto 8].
Qed.


Theorem typed_shift_value_progress :
  forall rightshift bge p cenv Gamma Sigma vm m first last ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (shift_operator rightshift)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  exists v,
    ssem_expr bge p vm m
      (Prim (Bop (shift_operator rightshift)) (Val first ty :: Val last ty :: nil) ty)
      m vm (Val v ty) /\ type_expr cenv Gamma Sigma (Val v ty) nil ty.
Proof.
  intros rightshift bge p cenv Gamma Sigma vm m first last ty ef Htyped.
  destruct (shift_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - apply shift32_value_progress.
  - exists (Vint64 (guarded_shift64_result rightshift s i j)).
    apply shift64_value_progress.
Qed.


Theorem typed_shift_value_preservation :
  forall rightshift bge p cenv Gamma Sigma vm m first last ty ef vm' m' e',
  type_expr cenv Gamma Sigma
    (Prim (Bop (shift_operator rightshift)) (Val first ty :: Val last ty :: nil) ty) ef ty ->
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift)) (Val first ty :: Val last ty :: nil) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros rightshift bge p cenv Gamma Sigma vm m first last ty ef vm' m' e' Htyped Hstep.
  destruct (shift_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hfirst Hlast)
    as [[sz [s [a [i [j [Hty [Hone Htwo]]]]]]] | [s [a [i [j [Hty [Hone Htwo]]]]]]];
    subst ty first last.
  - destruct (shift32_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
  - destruct (shift64_value_step_result _ _ _ _ _ _ _ _ _ _ _ _ Hstep)
      as [Hm [Hvm He]]. subst m' vm' e'. repeat split; try reflexivity; constructor.
Qed.


Theorem shift_progress_from_operands :
  forall rightshift bge p cenv Gamma Sigma vm m left right ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (shift_operator rightshift)) (left :: right :: nil) ty) ef ty ->
  ((exists v annotation, left = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m left m' vm' e') ->
  ((exists v annotation, right = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m right m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m
    (Prim (Bop (shift_operator rightshift)) (left :: right :: nil) ty) m' vm' e'.
Proof.
  intros rightshift bge p cenv Gamma Sigma vm m left right ty ef Htyped Hleft Hright.
  destruct (shift_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hfirst Hlast]]]]].
  eapply binary_progress_from_operands; [exact Hfirst | exact Hlast | exact Hleft | exact Hright |].
  intros first last Hone Htwo. subst left right.
  destruct (typed_shift_value_progress _ bge p _ _ _ vm m _ _ _ _ Htyped) as [v [Hstep Htype]].
  eauto.
Qed.


Theorem shift_preservation_from_operands :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma
    (Prim (Bop (shift_operator op)) (left :: right :: nil) ty) ef ty ->
  (forall operand operandEffect,
    (operand = left \/ operand = right) ->
    type_expr cenv Gamma Sigma operand operandEffect ty ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect ty /\
        sub_effect nextEffect operandEffect = true) ->
  ssem_expr bge p vm m
    (Prim (Bop (shift_operator op)) (left :: right :: nil) ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q op bge p cenv Gamma Sigma vm m left right ty ef vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (shift_typing_components _ _ _ _ _ _ _ _ Htyped)
    as [Hnumeric [ef1 [ef2 [Heffect [Hleft Hright]]]]]. subst ef.
  eapply binary_preservation_from_operands;
    [exact Hstate | exact Hleft | exact Hright | | exact Hlocal | | exact Hstep].
  - intros nextSigma nextLeft nextRight nextEf1 nextEf2 Hfirst Hlast.
    destruct op; constructor; assumption.
  - intros first a last b Hone Htwo nextM nextVm nextExpr Hs.
    subst left right.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Ha.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as Hb.
    simpl in Ha, Hb. subst a b.
    eapply typed_shift_value_preservation; [exact Htyped | exact Hs].
Qed.

Print Assumptions typed_shift_value_progress.

Print Assumptions typed_shift_value_preservation.

Print Assumptions shift_progress_from_operands.

Print Assumptions shift_preservation_from_operands.

Lemma promoted_integer_comparison_value_progress : forall bge p vm m i j c sz s a,
  ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c))
      (Val (Vint i) (Vtype (Tint sz s a)) ::
       Val (Vint j) (Vtype (Tint sz s a)) :: nil) (Vtype Tbool))
    m vm (Val (Vbool (match promoted_integer_signedness sz s with
      | Signed => Int.cmp c i j | Unsigned => Int.cmpu c i j end)) (Vtype Tbool)).
Proof.
  intros. destruct c, sz, s;
  eapply ssem_bop3_safe with (cenv := PTree.empty Ctypes.composite);
    try reflexivity.
  all: simpl; apply decode_boolean_of_bool.
Qed.

Definition comparison_operand_allowed c ty :=
  match c with
  | Ceq | Cne => (is_primint ty || is_primlong ty || is_primbool ty)%bool
  | _ => (is_primint ty || is_primlong ty)%bool
  end.

Lemma comparison_typing_components : forall c cenv Gamma Sigma left right ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (comparison_operator c)) (left :: right :: nil) (Vtype Tbool)) ef (Vtype Tbool) ->
  exists ty ef1 ef2, comparison_operand_allowed c ty = true /\ ef = ef1 ++ ef2 /\
    type_expr cenv Gamma Sigma left ef1 ty /\ type_expr cenv Gamma Sigma right ef2 ty.
Proof.
  intros c cenv Gamma Sigma left right ef Htyped.
  destruct c; inversion Htyped; subst; do 3 eexists; repeat split; eassumption.
Qed.

Lemma comparison_value_progress_from_types :
  forall c bge p cenv Gamma Sigma vm m first last ty ef1 ef2,
  comparison_operand_allowed c ty = true ->
  type_expr cenv Gamma Sigma (Val first ty) ef1 ty ->
  type_expr cenv Gamma Sigma (Val last ty) ef2 ty ->
  exists v, ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c)) (Val first ty :: Val last ty :: nil) (Vtype Tbool))
      m vm (Val v (Vtype Tbool)) /\
    type_expr cenv Gamma Sigma (Val v (Vtype Tbool)) nil (Vtype Tbool).
Proof.
  intros c bge p cenv Gamma Sigma vm m first last ty ef1 ef2 Hallowed Hfirst Hlast.
  pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hfirst) as Hshape1.
  pose proof (type_rel_typeof_val _ _ _ _ _ _ _ Hlast) as Hshape2.
  destruct ty; try solve [destruct c; discriminate Hallowed].
  destruct p0 as [|sz s a|s a];
    destruct first as [|b1|i1|l1|block1 ofs1|o1];
    destruct last as [|b2|i2|l2|block2 ofs2|o2];
    simpl in Hshape1, Hshape2; try contradiction.
  - destruct c; try discriminate Hallowed.
    + exists (Vbool (Bool.eqb b1 b2)). apply bool_eq_value_progress_preservation.
    + exists (Vbool (negb (Bool.eqb b1 b2))). apply bool_ne_value_progress_preservation.
  - eexists. split; [apply promoted_integer_comparison_value_progress | constructor].
  - eexists. split; [apply int64_comparison_value_progress | constructor].
Qed.

Print Assumptions comparison_value_progress_from_types.

Theorem comparison_progress_from_operands :
  forall c bge p cenv Gamma Sigma vm m left right ef,
  type_expr cenv Gamma Sigma
    (Prim (Bop (comparison_operator c)) (left :: right :: nil) (Vtype Tbool)) ef (Vtype Tbool) ->
  ((exists v annotation, left = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m left m' vm' e') ->
  ((exists v annotation, right = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m right m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c)) (left :: right :: nil) (Vtype Tbool)) m' vm' e'.
Proof.
  intros c bge p cenv Gamma Sigma vm m left right ef Htyped Hleft Hright.
  destruct (comparison_typing_components _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Hallowed [Heffect [Hfirst Hlast]]]]]].
  eapply binary_progress_from_operands; [exact Hfirst | exact Hlast | exact Hleft | exact Hright |].
  intros first last Hone Htwo. subst left right.
  destruct (comparison_value_progress_from_types c bge p cenv Gamma Sigma vm m
    first last ty ef1 ef2 Hallowed Hfirst Hlast) as [v [Hstep Htype]].
  eauto.
Qed.

Theorem comparison_preservation_from_operands :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    c bge p cenv Gamma Sigma vm m left right ef vm' m' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma
    (Prim (Bop (comparison_operator c)) (left :: right :: nil) (Vtype Tbool)) ef (Vtype Tbool) ->
  (forall operand operandEffect operandTy,
    (operand = left \/ operand = right) ->
    type_expr cenv Gamma Sigma operand operandEffect operandTy ->
    forall nextVm nextM nextOperand,
      ssem_expr bge p vm m operand nextM nextVm nextOperand ->
      exists nextSigma nextEffect,
        store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
        type_expr cenv Gamma nextSigma nextOperand nextEffect operandTy /\
        sub_effect nextEffect operandEffect = true) ->
  ssem_expr bge p vm m
    (Prim (Bop (comparison_operator c)) (left :: right :: nil) (Vtype Tbool)) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' (Vtype Tbool) /\ sub_effect ef' ef = true.
Proof.
  intros Q c bge p cenv Gamma Sigma vm m left right ef vm' m' e'
    Hstate Htyped Hlocal Hstep.
  destruct (comparison_typing_components _ _ _ _ _ _ _ Htyped)
    as [ty [ef1 [ef2 [Hallowed [Heffect [Hleft Hright]]]]]]. subst ef.
  eapply binary_preservation_from_operands;
    [exact Hstate | exact Hleft | exact Hright | | | | exact Hstep].
  - intros nextSigma nextLeft nextRight nextEf1 nextEf2 Hfirst Hlast.
    destruct c; econstructor; eassumption.
  - intros. eapply Hlocal; eassumption.
  - intros first a last b Hone Htwo nextM nextVm nextExpr Hs.
    subst left right.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hleft) as Ha.
    pose proof (type_rel_typeof _ _ _ _ _ _ Hright) as Hb.
    simpl in Ha, Hb. subst a b.
    eapply comparison_value_preservation; exact Hs.
Qed.

Print Assumptions comparison_progress_from_operands.
Print Assumptions comparison_preservation_from_operands.

Definition integer_unary_operator (complement : bool) :=
  if complement then Onotint else Oneg.
Definition integer_unary32_result (complement : bool) i :=
  if complement then Int.not i else Int.neg i.
Definition integer_unary64_result (complement : bool) i :=
  if complement then Int64.not i else Int64.neg i.

Lemma integer_unary32_operation : forall complement sz s a i m,
  sem_unary_operation (integer_unary_operator complement) (Values.Vint i) (Ctypes.Tint sz s a) m =
    Some (Values.Vint (integer_unary32_result complement i)).
Proof. intros; destruct complement, sz, s; reflexivity. Qed.

Lemma integer_unary64_operation : forall complement s a i m,
  sem_unary_operation (integer_unary_operator complement) (Values.Vlong i) (Ctypes.Tlong s a) m =
    Some (Values.Vlong (integer_unary64_result complement i)).
Proof. intros; destruct complement, s; reflexivity. Qed.

Lemma integer_unary_typing_components : forall complement cenv Gamma Sigma e ef ty,
  type_expr cenv Gamma Sigma (Prim (Uop (integer_unary_operator complement)) (e :: nil) ty) ef ty ->
  (is_primint ty || is_primlong ty)%bool = true /\ type_expr cenv Gamma Sigma e ef ty.
Proof. intros; destruct complement; inversion H; subst; auto. Qed.

Lemma integer_unary32_decode : forall complement i,
  decode_unary_result (integer_unary_operator complement) (Values.Vint i) = OK (Vint i).
Proof. intros; destruct complement; reflexivity. Qed.
Lemma integer_unary64_decode : forall complement i,
  decode_unary_result (integer_unary_operator complement) (Values.Vlong i) = OK (Vint64 i).
Proof. intros; destruct complement; reflexivity. Qed.

Theorem typed_integer_unary_value_progress :
  forall complement bge p cenv Gamma Sigma vm m v ty ef,
  type_expr cenv Gamma Sigma
    (Prim (Uop (integer_unary_operator complement)) (Val v ty :: nil) ty) ef ty ->
  exists v', ssem_expr bge p vm m
    (Prim (Uop (integer_unary_operator complement)) (Val v ty :: nil) ty) m vm (Val v' ty) /\
    type_expr cenv Gamma Sigma (Val v' ty) nil ty.
Proof.
  intros complement bge p cenv Gamma Sigma vm m v ty ef Htyped.
  destruct (integer_unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hnumeric Hvalue].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hvalue Hvalue)
    as [[sz [s [a [i [j [Hty [Hv Hj]]]]]]] | [s [a [i [j [Hty [Hv Hj]]]]]]]; subst ty v.
  - exists (Vint (integer_unary32_result complement i)). split; [|constructor].
    eapply ssem_uop2; [reflexivity | | apply integer_unary32_decode].
    cbn [trans_bvalue_cvalue transBeePL_type]. apply integer_unary32_operation.
  - exists (Vint64 (integer_unary64_result complement i)). split; [|constructor].
    eapply ssem_uop2; [reflexivity | | apply integer_unary64_decode].
    cbn [trans_bvalue_cvalue transBeePL_type]. apply integer_unary64_operation.
Qed.

Theorem typed_integer_unary_value_preservation :
  forall complement bge p cenv Gamma Sigma vm m v ty ef m' vm' e',
  type_expr cenv Gamma Sigma
    (Prim (Uop (integer_unary_operator complement)) (Val v ty :: nil) ty) ef ty ->
  ssem_expr bge p vm m
    (Prim (Uop (integer_unary_operator complement)) (Val v ty :: nil) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros complement bge p cenv Gamma Sigma vm m v ty ef m' vm' e' Htyped Hstep.
  destruct (integer_unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hnumeric Hvalue].
  destruct (typed_numeric_value_pair _ _ _ _ _ _ _ _ Hnumeric Hvalue Hvalue)
    as [[sz [s [a [i [j [Hty [Hv Hj]]]]]]] | [s [a [i [j [Hty [Hv Hj]]]]]]]; subst ty v;
    inversion Hstep; subst;
    try solve [exfalso; eapply value_has_no_small_step; eauto].
  - match goal with Hsem : sem_unary_operation _ _ _ _ = Some _ |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite integer_unary32_operation in Hsem; inversion Hsem; subst
    end.
    match goal with Hd : decode_unary_result _ _ = OK _ |- _ =>
      rewrite integer_unary32_decode in Hd; inversion Hd; subst
    end. repeat split; try reflexivity; constructor.
  - match goal with Hsem : sem_unary_operation _ _ _ _ = Some _ |- _ =>
      cbn [trans_bvalue_cvalue transBeePL_type] in Hsem;
      rewrite integer_unary64_operation in Hsem; inversion Hsem; subst
    end.
    match goal with Hd : decode_unary_result _ _ = OK _ |- _ =>
      rewrite integer_unary64_decode in Hd; inversion Hd; subst
    end. repeat split; try reflexivity; constructor.
Qed.

Print Assumptions typed_integer_unary_value_progress.
Print Assumptions typed_integer_unary_value_preservation.

Lemma unary_typing_components : forall op cenv Gamma Sigma operand ef ty,
  type_expr cenv Gamma Sigma (Prim (Uop op) (operand :: nil) ty) ef ty ->
  type_expr cenv Gamma Sigma operand ef ty /\
  (forall nextSigma nextOperand nextEffect,
    type_expr cenv Gamma nextSigma nextOperand nextEffect ty ->
    type_expr cenv Gamma nextSigma (Prim (Uop op) (nextOperand :: nil) ty) nextEffect ty).
Proof.
  intros op cenv Gamma Sigma operand ef ty Htyped.
  inversion Htyped; subst; split; [assumption | | assumption | | assumption |];
    intros; econstructor; eauto.
Qed.

Theorem typed_unary_value_progress : forall op bge p cenv Gamma Sigma vm m v ty ef,
  type_expr cenv Gamma Sigma (Prim (Uop op) (Val v ty :: nil) ty) ef ty ->
  exists v', ssem_expr bge p vm m (Prim (Uop op) (Val v ty :: nil) ty) m vm (Val v' ty) /\
    type_expr cenv Gamma Sigma (Val v' ty) nil ty.
Proof.
  intros op bge p cenv Gamma Sigma vm m v ty ef Htyped. destruct op.
  - inversion Htyped; subst.
    match goal with Hv : type_expr _ _ _ (Val _ _) _ _ |- _ => inversion Hv; subst end.
    eexists. apply notbool_value_progress_preservation.
  - eapply typed_integer_unary_value_progress with (complement := true); exact Htyped.
  - eapply typed_integer_unary_value_progress with (complement := false); exact Htyped.
  - inversion Htyped.
Qed.

Theorem typed_unary_value_preservation :
  forall op bge p cenv Gamma Sigma vm m v ty ef m' vm' e',
  type_expr cenv Gamma Sigma (Prim (Uop op) (Val v ty :: nil) ty) ef ty ->
  ssem_expr bge p vm m (Prim (Uop op) (Val v ty :: nil) ty) m' vm' e' ->
  m' = m /\ vm' = vm /\ type_expr cenv Gamma Sigma e' nil ty.
Proof.
  intros op bge p cenv Gamma Sigma vm m v ty ef m' vm' e' Htyped Hstep. destruct op.
  - inversion Htyped; subst.
    match goal with Hv : type_expr _ _ _ (Val _ _) _ _ |- _ => inversion Hv; subst end.
    eapply notbool_value_preservation; exact Hstep.
  - eapply typed_integer_unary_value_preservation with (complement := true); eassumption.
  - eapply typed_integer_unary_value_preservation with (complement := false); eassumption.
  - inversion Htyped.
Qed.

Theorem unary_progress_from_operand :
  forall op bge p cenv Gamma Sigma vm m operand ef ty,
  type_expr cenv Gamma Sigma (Prim (Uop op) (operand :: nil) ty) ef ty ->
  ((exists v annotation, operand = Val v annotation) \/
    exists m' vm' e', ssem_expr bge p vm m operand m' vm' e') ->
  exists m' vm' e', ssem_expr bge p vm m (Prim (Uop op) (operand :: nil) ty) m' vm' e'.
Proof.
  intros op bge p cenv Gamma Sigma vm m operand ef ty Htyped Hprogress.
  destruct (unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hoperand Hrebuild].
  pose proof (type_rel_typeof _ _ _ _ _ _ Hoperand) as Hannotation.
  destruct Hprogress as [[v [annotation He]] | [nextM [nextVm [nextOperand Hstep]]]].
  - subst operand. simpl in Hannotation. subst annotation.
    destruct (typed_unary_value_progress op bge p cenv Gamma Sigma vm m v ty ef Htyped)
      as [v' [Hs Hv]]. eauto.
  - rewrite <- Hannotation. do 3 eexists. apply ssem_uop1; exact Hstep.
Qed.

Theorem unary_preservation_from_operand :
  forall (Q : store_context -> vmap -> Memory.mem -> Prop)
    op bge p cenv Gamma Sigma vm m operand ef ty m' vm' e',
  Q Sigma vm m ->
  type_expr cenv Gamma Sigma (Prim (Uop op) (operand :: nil) ty) ef ty ->
  (forall nextVm nextM nextOperand,
    ssem_expr bge p vm m operand nextM nextVm nextOperand ->
    exists nextSigma nextEffect,
      store_context_extends Sigma nextSigma /\ Q nextSigma nextVm nextM /\
      type_expr cenv Gamma nextSigma nextOperand nextEffect ty /\ sub_effect nextEffect ef = true) ->
  ssem_expr bge p vm m (Prim (Uop op) (operand :: nil) ty) m' vm' e' ->
  exists Sigma' ef', store_context_extends Sigma Sigma' /\ Q Sigma' vm' m' /\
    type_expr cenv Gamma Sigma' e' ef' ty /\ sub_effect ef' ef = true.
Proof.
  intros Q op bge p cenv Gamma Sigma vm m operand ef ty m' vm' e'
    Hstate Htyped Hlocal Hstep.
  destruct (unary_typing_components _ _ _ _ _ _ _ Htyped) as [Hoperand Hrebuild].
  inversion Hstep; subst.
  - match goal with Hs : ssem_expr bge p vm m operand _ _ _ |- _ =>
      destruct (Hlocal _ _ _ Hs) as [nextSigma [nextEffect [Hext [Hstate' [Htyped' Hsub]]]]]
    end.
    exists nextSigma, nextEffect. repeat split; try assumption. apply Hrebuild; exact Htyped'.
  - edestruct typed_unary_value_preservation as [_ [_ Hresult]];
      [exact Htyped | exact Hstep |].
    exists Sigma, nil. split; [apply store_context_extends_refl |].
    split; [exact Hstate |]. split; [exact Hresult | apply sub_effect_nil].
Qed.

Print Assumptions typed_unary_value_progress.
Print Assumptions typed_unary_value_preservation.
Print Assumptions unary_progress_from_operand.
Print Assumptions unary_preservation_from_operand.
