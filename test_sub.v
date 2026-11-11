
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.

Definition _h : ident := $"h".
Definition _scanf : ident := $"scanf".
Definition _printf : ident := $"printf".
Definition _htons : ident := $"htons".
Definition _bpf_probe_read_user_str : ident := $"bpf_probe_read_user_str".
Definition _bpf_printk : ident := $"bpf_printk".
Definition _bpf_map_update_elem : ident := $"bpf_map_update_elem".
Definition _bpf_map_lookup_elem : ident := $"bpf_map_lookup_elem".
Definition _bpf_ktime_get_ns : ident := $"bpf_ktime_get_ns".
Definition _bpf_get_prandom_u32 : ident := $"bpf_get_prandom_u32".
Definition _bpf_get_current_pid_tgid : ident := $"bpf_get_current_pid_tgid".
Definition _bpf_get_current_comm : ident := $"bpf_get_current_comm".
Definition _z : ident := $"z".
Definition _y : ident := $"y".
Definition _x : ident := $"x".
Definition _main : ident := $"main".
Definition ident_to_string := ((_h, "h") :: (_scanf, "scanf") :: (_printf, "printf") :: (_htons, "htons") :: (_bpf_probe_read_user_str, "bpf_probe_read_user_str") :: (_bpf_printk, "bpf_printk") :: (_bpf_map_update_elem, "bpf_map_update_elem") :: (_bpf_map_lookup_elem, "bpf_map_lookup_elem") :: (_bpf_ktime_get_ns, "bpf_ktime_get_ns") :: (_bpf_get_prandom_u32, "bpf_get_prandom_u32") :: (_bpf_get_current_pid_tgid, "bpf_get_current_pid_tgid") :: (_bpf_get_current_comm, "bpf_get_current_comm") :: (_z, "z") :: (_y, "y") :: (_x, "x") :: (_main, "main") :: nil).



Definition bcomposites : list bcomposite_definition := nil.


Definition bpf_get_current_comm_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_get_current_comm" {| bsig_args := Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Unsigned dattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tlong Signed dattr); bsig_cc := cc_default |}.

Definition ext_bpf_get_current_comm : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_get_current_comm_ef
                           (Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Unsigned dattr) :: nil)
                           (Vtype (BeeTypes.Tlong Signed dattr))
                           (cc_default)).

Definition bpf_get_current_pid_tgid_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_get_current_pid_tgid" {| bsig_args := nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tlong Unsigned dattr); bsig_cc := cc_default |}.

Definition ext_bpf_get_current_pid_tgid : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_get_current_pid_tgid_ef
                           (nil)
                           (Vtype (BeeTypes.Tlong Unsigned dattr))
                           (cc_default)).

Definition bpf_get_prandom_u32_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_get_prandom_u32" {| bsig_args := nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tint I32 Unsigned dattr); bsig_cc := cc_default |}.

Definition ext_bpf_get_prandom_u32 : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_get_prandom_u32_ef
                           (nil)
                           (Vtype (BeeTypes.Tint I32 Unsigned dattr))
                           (cc_default)).

Definition bpf_ktime_get_ns_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_ktime_get_ns" {| bsig_args := nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tlong Unsigned dattr); bsig_cc := cc_default |}.

Definition ext_bpf_ktime_get_ns : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_ktime_get_ns_ef
                           (nil)
                           (Vtype (BeeTypes.Tlong Unsigned dattr))
                           (cc_default)).

Definition bpf_map_lookup_elem_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_map_lookup_elem" {| bsig_args := Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tlong Unsigned dattr); bsig_cc := cc_default |}.

Definition ext_bpf_map_lookup_elem : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_map_lookup_elem_ef
                           (Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: nil)
                           (Vtype (BeeTypes.Tlong Unsigned dattr))
                           (cc_default)).

Definition bpf_map_update_elem_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_map_update_elem" {| bsig_args := Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tint I32 Signed dattr); bsig_cc := cc_default |}.

Definition ext_bpf_map_update_elem : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_map_update_elem_ef
                           (Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: Vtype (BeeTypes.Tlong Unsigned dattr) :: nil)
                           (Vtype (BeeTypes.Tint I32 Signed dattr))
                           (cc_default)).

Definition bpf_printk_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_printk" {| bsig_args := Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Signed dattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tint I32 Signed dattr); bsig_cc := cc_vararg |}.

Definition ext_bpf_printk : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_printk_ef
                           (Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Signed dattr) :: nil)
                           (Vtype (BeeTypes.Tint I32 Signed dattr))
                           (cc_vararg)).

Definition bpf_probe_read_user_str_ef : BeePL.external_function :=
  BeePL.EF_external "bpf_probe_read_user_str" {| bsig_args := Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Unsigned dattr) :: Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tlong Signed dattr); bsig_cc := cc_default |}.

Definition ext_bpf_probe_read_user_str : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External bpf_probe_read_user_str_ef
                           (Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: Vtype (BeeTypes.Tint I32 Unsigned dattr) :: Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil)
                           (Vtype (BeeTypes.Tlong Signed dattr))
                           (cc_default)).

Definition htons_ef : BeePL.external_function :=
  BeePL.EF_external "htons" {| bsig_args := Vtype (BeeTypes.Tint I16 Unsigned dattr) :: nil; bsig_ef := nil; bsig_res := Vtype (BeeTypes.Tint I16 Unsigned dattr); bsig_cc := cc_default |}.

Definition ext_htons : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External htons_ef
                           (Vtype (BeeTypes.Tint I16 Unsigned dattr) :: nil)
                           (Vtype (BeeTypes.Tint I16 Unsigned dattr))
                           (cc_default)).

Definition printf_ef : BeePL.external_function :=
  BeePL.EF_external "printf" {| bsig_args := Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tint I32 Signed dattr); bsig_cc := cc_vararg |}.

Definition ext_printf : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External printf_ef
                           (Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil)
                           (Vtype (BeeTypes.Tint I32 Signed dattr))
                           (cc_vararg)).

Definition scanf_ef : BeePL.external_function :=
  BeePL.EF_external "scanf" {| bsig_args := Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil; bsig_ef := Io :: nil; bsig_res := Vtype (BeeTypes.Tint I32 Signed dattr); bsig_cc := cc_vararg |}.

Definition ext_scanf : AST.globdef BeePL.fundef type :=
  AST.Gfun (BeePL.External scanf_ef
                           (Ptrtype (Reftype (Bprim (BeeTypes.Tint I8 Signed dattr)) noattr) :: nil)
                           (Vtype (BeeTypes.Tint I32 Signed dattr))
                           (cc_vararg)).

Definition f_main : BeePL.function := {| 
  fn_return := Vtype (BeeTypes.Tint I32 Signed dattr);
  fn_effect := nil;
  fn_callconv := cc_default;
  fn_args := nil;
  fn_vars := (_x, Vtype (BeeTypes.Tint I32 Signed dattr)) :: (_y, Vtype (BeeTypes.Tint I32 Signed dattr)) :: (_z, Vtype (BeeTypes.Tint I32 Signed dattr)) :: nil;
  fn_body := (Bind _x (Vtype (BeeTypes.Tint I32 Signed dattr))
                  (Const (ConsInt (Int.repr 5)) (Vtype (BeeTypes.Tint I32 Signed dattr)))
                  (Bind _y (Vtype (BeeTypes.Tint I32 Signed dattr))
                  (Const (ConsInt (Int.repr 3)) (Vtype (BeeTypes.Tint I32 Signed dattr)))
                  (Bind _z (Vtype (BeeTypes.Tint I32 Signed dattr))
                  (Prim (Bop Cop.Osub)
                  ((Var _x (Vtype (BeeTypes.Tint I32 Signed dattr))) :: (Var _y (Vtype (BeeTypes.Tint I32 Signed dattr))) :: nil)
                  (Vtype (BeeTypes.Tint I32 Signed dattr)))
                  (Var _z (Vtype (BeeTypes.Tint I32 Signed dattr)))
             (Vtype (BeeTypes.Tint I32 Signed dattr)))
             (Vtype (BeeTypes.Tint I32 Signed dattr)))
             (Vtype (BeeTypes.Tint I32 Signed dattr)));
  is_ebpf := false
|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) :=
  (_bpf_get_current_comm, ext_bpf_get_current_comm, None) ::
  (_bpf_get_current_pid_tgid, ext_bpf_get_current_pid_tgid, None) ::
  (_bpf_get_prandom_u32, ext_bpf_get_prandom_u32, None) ::
  (_bpf_ktime_get_ns, ext_bpf_ktime_get_ns, None) ::
  (_bpf_map_lookup_elem, ext_bpf_map_lookup_elem, None) ::
  (_bpf_map_update_elem, ext_bpf_map_update_elem, None) ::
  (_bpf_printk, ext_bpf_printk, None) ::
  (_bpf_probe_read_user_str, ext_bpf_probe_read_user_str, None) ::
  (_htons, ext_htons, None) ::
  (_printf, ext_printf, None) ::
  (_scanf, ext_scanf, None) ::
  (_main, AST.Gfun (BeePL.Internal f_main), None) :: nil.

Definition public_idents : list ident := (_main :: nil).


Lemma bcomposite_correct : wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed. 

Definition bprogram : BeePL.program := @mkbprogram bcomposites
                                        global_definitions
                                        public_idents
                                        _main
                                        bcomposite_correct
                                        ident_to_string.
