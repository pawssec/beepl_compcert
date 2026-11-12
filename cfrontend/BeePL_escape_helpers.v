(* Explicit trusted ABI contracts for synchronous helpers. This checker does
   not prove external implementation behavior or source typing. The caller
   must resolve the actual global callee and validate the source program.
   Unknown externals, libc variadic I/O, and indirect callees fail closed. *)
Require Import List String Bool ZArith AST Ctypes Integers.
Require Import BeeTypes BeePL_values BeePL.
Import ListNotations.
Local Open Scope string_scope.

Definition helper_attr_eq (a b:attr) : bool := if Ctypes.attr_eq a b then true else false.

Definition helper_i8 := Vtype(Tint I8 Signed noattr).
Definition helper_i32 := Vtype(Tint I32 Signed noattr).
Definition helper_u16 := Vtype(Tint I16 Unsigned noattr).
Definition helper_u32 := Vtype(Tint I32 Unsigned noattr).
Definition helper_long := Vtype(Tlong Signed noattr).
Definition helper_ulong := Vtype(Tlong Unsigned noattr).
Definition helper_ref (p:primitive_type) := Ptrtype(Reftype(Bprim p) noattr).
Definition helper_charptr := helper_ref(Tint I8 Signed noattr).
Definition helper_keyptr := helper_ref(Tint I32 Unsigned noattr).
Definition helper_valueptr := helper_ref(Tlong Unsigned noattr).
Definition helper_map := Atype helper_u32 8 noattr.

Record synchronous_contract := {
  helper_formals : list type;
  helper_result : type;
  helper_effects : effect;
  helper_variadic : bool
}.
Definition helper_spec ts rt ef va : synchronous_contract :=
  {|helper_formals:=ts; helper_result:=rt; helper_effects:=ef; helper_variadic:=va|}.

Definition helper_skb_type names (ty:type) : bool :=
  match ty with
  | Ptrtype(Reftype(Bstruct id a) pa) =>
      helper_attr_eq a noattr && helper_attr_eq pa noattr &&
      existsb (fun entry => Pos.eqb id (fst entry) && String.eqb(snd entry) "__sk_buff") names
  | _ => false
  end.

Definition synchronous_helper_contract names name (declared:list type)
    : option synchronous_contract :=
  if String.eqb name "bpf_get_prandom_u32" then Some(helper_spec [] helper_u32 [Io] false) else
  if String.eqb name "bpf_ktime_get_ns" || String.eqb name "bpf_get_current_pid_tgid"
    then Some(helper_spec [] helper_ulong [Io] false) else
  if String.eqb name "htons" then Some(helper_spec [helper_u16] helper_u16 [] false) else
  if String.eqb name "bpf_printk" then Some(helper_spec [helper_charptr;helper_i32] helper_i32 [Io] true) else
  if String.eqb name "bpf_get_current_comm" then Some(helper_spec [helper_charptr;helper_u32] helper_long [Io] false) else
  if String.eqb name "bpf_probe_read_user_str" then Some(helper_spec [helper_charptr;helper_u32;helper_charptr] helper_long [Io] false) else
  if String.eqb name "bpf_map_lookup_elem" then Some(helper_spec [helper_map;helper_keyptr]
    (Ptrtype(Otype(Reftype(Bprim(Tlong Unsigned noattr)) noattr))) [Read;Io] false) else
  if String.eqb name "bpf_map_update_elem" then Some(helper_spec [helper_map;helper_keyptr;helper_valueptr;helper_ulong] helper_long [Write;Io] false) else
  if String.eqb name "bpf_map_delete_elem" then Some(helper_spec [helper_map;helper_keyptr] helper_long [Write;Io] false) else
  if String.eqb name "bpf_redirect" then Some(helper_spec [helper_u32;helper_ulong] helper_long [Io] false) else
  match declared with
  | ctx::_ => if helper_skb_type names ctx then
      if String.eqb name "bpf_skb_change_type" then Some(helper_spec [ctx;helper_u32] helper_long [Write;Io] false) else
      if String.eqb name "bpf_skb_load_bytes" then Some(helper_spec [ctx;helper_u32;helper_keyptr;helper_u32] helper_long [Read;Write;Io] false) else
      if String.eqb name "bpf_skb_store_bytes" then Some(helper_spec [ctx;helper_u32;helper_keyptr;helper_u32;helper_ulong] helper_long [Read;Write;Io] false) else None
    else None
  | _ => None
  end.

Definition helper_actual_type (formal actual:type) : bool :=
  eq_type formal actual ||
  match formal,actual with
  | Ptrtype(Reftype(Bprim p) a),Atype(Vtype q) _ _ =>
      helper_attr_eq a noattr && eq_primitive_type p q
  | _,_ => false
  end.

Fixpoint helper_fixed_arguments (formals:list type) (args:list expr) : bool :=
  match formals,args with
  | [],_ => true
  | t::ts,e::es => helper_actual_type t (typeof_expr e) && helper_fixed_arguments ts es
  | _,_ => false
  end.

Definition helper_print_payload (e:expr) : bool :=
  match typeof_expr e with
  | Vtype(Tint _ _ _) | Vtype(Tlong _ _) | Ptrtype(Reftype _ _) => true
  | _ => false
  end.

Definition helper_literal (expected:type) (n:Z) (e:expr) : bool :=
  eq_type (typeof_expr e) expected &&
  match e with
  | Const(ConsInt v) _ => Z.eqb(Int.signed v)n
  | Const(ConsLong v) _ => Z.eqb(Int64.signed v)n
  | Prim(Cast target)[Const(ConsInt v) _] _ => eq_type target expected && Z.eqb(Int.signed v)n
  | Prim(Cast target)[Const(ConsLong v) _] _ => eq_type target expected && Z.eqb(Int64.signed v)n
  | _ => false
  end.

Definition helper_argument_constraints name args : bool :=
  if String.eqb name "bpf_skb_load_bytes" then
    match args with [_;_;_;len] => helper_literal helper_u32 4 len | _ => false end
  else if String.eqb name "bpf_skb_store_bytes" then
    match args with [_;_;_;len;flags] => helper_literal helper_u32 4 len && helper_literal helper_ulong 0 flags | _ => false end
  else if String.eqb name "bpf_redirect" then
    match args with [_;flags] => helper_literal helper_ulong 0 flags | _ => false end
  else true.

Definition helper_cc_ok (cc:calling_convention) (va:bool) : bool :=
  (match cc_vararg cc with None => negb va | Some n => va && Z.eqb n 1 end) &&
  Bool.eqb (cc_unproto cc) va && negb (cc_structret cc).

Definition synchronous_helper_call names (resolved:BeePL.fundef) (args:list expr) : bool :=
  match resolved with
  | External (EF_external name sig) declared result cc =>
    match synchronous_helper_contract names name declared with
    | None => false
    | Some contract =>
      eq_types eq_type declared (helper_formals contract) &&
      eq_types eq_type (bsig_args sig) declared &&
      eq_type result (helper_result contract) && eq_type (bsig_res sig) result &&
      eq_effect (bsig_ef sig) (helper_effects contract) &&
      helper_cc_ok cc (helper_variadic contract) &&
      (if calling_convention_eq (bsig_cc sig) cc then true else false) &&
      helper_fixed_arguments declared args &&
      (if helper_variadic contract then
         (Nat.leb (List.length declared) (List.length args) &&
          Nat.leb (List.length args) (List.length declared+3) &&
          forallb helper_print_payload (skipn (List.length declared) args))
       else Nat.eqb (List.length args) (List.length declared)) &&
      helper_argument_constraints name args
    end
  | Internal _ => false
  end.

Lemma synchronous_helpers_reject_internal : forall names fn args,
  synchronous_helper_call names (Internal fn) args=false.
Proof. reflexivity. Qed.

Lemma synchronous_helpers_require_contract : forall names name sig declared result cc args,
  synchronous_helper_call names (External(EF_external name sig)declared result cc) args=true ->
  exists contract, synchronous_helper_contract names name declared=Some contract.
Proof.
  intros. unfold synchronous_helper_call in H.
  destruct(synchronous_helper_contract names name declared) as [c|] eqn:E;
    [eauto|discriminate].
Qed.

Definition helper_test_external name ts rt ef : BeePL.fundef :=
  External (EF_external name {|bsig_args:=ts;bsig_res:=rt;bsig_ef:=ef;
    bsig_cc:=cc_default|}) ts rt cc_default.

Example helper_accepts_scalar_map_update :
  synchronous_helper_call []
    (helper_test_external "bpf_map_update_elem"
      [helper_map;helper_keyptr;helper_valueptr;helper_ulong] helper_long [Write;Io])
    [Var 1%positive helper_map; Var 2%positive helper_keyptr;
     Var 3%positive helper_valueptr; Const(ConsLong Int64.zero) helper_ulong]=true.
Proof. vm_compute; reflexivity. Qed.

Example helper_rejects_pointer_value_map_signature :
  synchronous_helper_call []
    (helper_test_external "bpf_map_update_elem"
      [helper_map;helper_keyptr;Ptrtype(Reftype(Bstruct 7%positive noattr)noattr);helper_ulong]
      helper_long [Write;Io])
    [Var 1%positive helper_map;Var 2%positive helper_keyptr;
     Var 3%positive (Ptrtype(Reftype(Bstruct 7%positive noattr)noattr));
     Const(ConsLong Int64.zero) helper_ulong]=false.
Proof. vm_compute; reflexivity. Qed.

Definition helper_test_skb := Ptrtype(Reftype(Bstruct 9%positive noattr)noattr).
Definition helper_test_skb_store len :=
  synchronous_helper_call [(9%positive,"__sk_buff")]
    (helper_test_external "bpf_skb_store_bytes"
      [helper_test_skb;helper_u32;helper_keyptr;helper_u32;helper_ulong]
      helper_long [Read;Write;Io])
    [Var 1%positive helper_test_skb;Const(ConsInt Int.zero)helper_u32;
     Var 2%positive helper_keyptr;
     Prim(Cast helper_u32)[Const(ConsInt(Int.repr len))helper_i32]helper_u32;
     Prim(Cast helper_ulong)[Const(ConsInt Int.zero)helper_i32]helper_ulong].

Example helper_accepts_four_byte_skb_store : helper_test_skb_store 4=true.
Proof. vm_compute; reflexivity. Qed.
Example helper_rejects_oversized_skb_store : helper_test_skb_store 8=false.
Proof. vm_compute; reflexivity. Qed.

Example helper_rejects_unknown_external :
  synchronous_helper_call []
    (helper_test_external "retain_pointer" [helper_keyptr] Utype [])
    [Var 1%positive helper_keyptr]=false.
Proof. vm_compute; reflexivity. Qed.

Example helper_rejects_inconsistent_embedded_signature :
  synchronous_helper_call []
    (External (EF_external "bpf_get_prandom_u32"
      {|bsig_args:=[helper_keyptr];bsig_res:=helper_u32;
        bsig_ef:=[Io];bsig_cc:=cc_default|}) [] helper_u32 cc_default) []=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions synchronous_helpers_require_contract.
Print Assumptions helper_accepts_scalar_map_update.
Print Assumptions helper_rejects_pointer_value_map_signature.
