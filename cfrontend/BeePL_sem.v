Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking Ctypes Smallstep.
Require Import Globalenvs Cop Csyntax Csem BeeTypes BeePL_aux BeePL_mem BeePL Csyntaxdefs Memory.
Require Import BeePL_packet.
Require Import Initializersproof Cstrategy BeePL_auxlemmas Coqlib Errors SimplExpr Events BeePL_values.

From mathcomp Require Import all_ssreflect. 

(* How to transform the heap into heap regions *)
(* heap_compcert : (l1 -> v1; l2 -> v2; .... ln -> vn)
heap_koka : ((h1, (l1 -> v1; l2 -> v2; .... ln -> vn);
        (h2, (l1 -> v1; l2 -> v2; .... ln -> vn);
        ..
!(h, e)*) 

Fixpoint is_stateful_expr (e : BeePL.expr) : bool :=
match e with 
| Val e t => true 
| Var x t => false
| Const c t => false
| App e es t => true 
| Prim b es t => match b with 
                 | Ref => true 
                 | Deref => true 
                 | Massgn => true 
                 | Uop o => true 
                 | Bop o => true
                 | Cast t => true
                 | ArrayRead _ => true
                 end
| Bind x tx e e' t => is_stateful_expr e || is_stateful_expr e' 
| Cond e1 e2 e3 t => is_stateful_expr e1 || is_stateful_expr e2 || is_stateful_expr e3   
| Unit t => false
| Addr l ofs t => false
| Sinit _ _ _ _ => true
| Sfield _ _ _ => true
| For e1 e2 d e t => is_stateful_expr e 
| Enone t => false
| Esome e t => is_stateful_expr e
| Match e ps es t => is_stateful_expr e || has is_stateful_expr es
| Ebytes es t => has is_stateful_expr es
| Ainit a t es t' => has is_stateful_expr es
| Aaccess a t n t' => true
| CallFrame _ _ _ => true
| LoopFrame _ _ _ => true
end.

Fixpoint is_stateful_exprs (es : list BeePL.expr) : bool :=
match es with 
| nil => true
| e :: es => is_stateful_expr e && is_stateful_exprs es
end.

Definition wrange d (n1 n2 : Z) : seq int :=
  let n := Z.to_nat (n2 - n1) in
  match d with
  | Up   => (map Int.repr [seq (Z.add n1 (Z.of_nat i)) | i <- iota 0 n])
  | Down => (map Int.repr [seq (Z.sub n2 (Z.of_nat i)) | i <- iota 0 n])
  end.

Definition check_unsafe_op (op : binary_operation) (s : signedness) (v1 v2 : value) : bool :=
match op with 
| Odiv => match s with 
         | Signed => if is_zero_val v2
                        || is_overflow_vals v1 v2
                     then true 
                     else false
         | Unsigned => is_zero_val v2
         end
| Omod => match s with 
         | Signed => if is_zero_val v2
                        || is_overflow_vals v1 v2
                     then true 
                     else false
         | Unsigned => is_zero_val v2
         end
| Oshl => is_val_shift v2
| Oshr => is_val_shift v2
| _ => false
end.


Definition extract_variables_globdef (gd : (globdef fundef type)) : list (ident * type) :=
match gd with 
| Gfun fd => match fd with 
             | Internal fn => fn.(fn_args) ++ fn.(fn_vars)
             | External ef ts t cc => nil
             end
| Gvar gv => nil
end.

Fixpoint extract_variables_globdefs (gds : list (globdef fundef type)) : list (ident * type) :=
match gds with 
| nil => nil
| gd :: gds => extract_variables_globdef gd ++ extract_variables_globdefs gds
end.

Fixpoint string_of_nat (n : nat) : string :=
match n with
| O => "0"%string
| S n' => append (string_of_nat n') "1"%string (* or a real digit encoder *)
end.

Fixpoint ident_in_list (x : ident) (l : list ident) {struct l} : bool :=
  match l with
  | nil => false
  | y :: ys => if (x =? y)%positive then true else ident_in_list x ys
  end.

Fixpoint create_fresh_ident_aux (used : list ident) (next : positive) (fuel : nat) : option ident :=
  match fuel with
  | O => None (* exhausted fuel *)
  | S fuel' =>
      if ident_in_list next used then
        create_fresh_ident_aux used (Pos.succ next) fuel'
      else
        Some next
  end.

Definition create_fresh_ident (used : list ident) : ident :=
  match create_fresh_ident_aux used 100%positive 10000 with
  | Some id => id
  | None => 1%positive (* fallback if we somehow exhaust fuel *)
  end.

Definition structure_result_type (sid : ident) (sa : attr) (t : type) : Prop :=
  t = Stype sid sa \/ exists pa, t = Ptrtype (Reftype (Bstruct sid sa) pa).

Inductive sem_allocate_fields (ge : genv) : positive -> ptrofs -> ident -> list ident -> list value -> list type -> Memory.mem -> Memory.mem -> Prop :=
| sem_allocate_nil : forall b ofs sid m,
                          sem_allocate_fields ge b ofs sid nil nil nil m m
| sem_allocate_struct : forall loc ofs sid co f delta bf fs v vs t ts m1 m2 m3,
                        ge.(genv_cenv)!sid = Some co ->
                        field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                        assign_addr ge t m1 loc (Ptrofs.add ofs (Ptrofs.repr delta)) bf v m2 v ->
                        sem_allocate_fields ge loc ofs sid fs vs ts m2 m3 ->
                        sem_allocate_fields ge loc ofs sid (f :: fs) (v :: vs) (t :: ts) m1 m3.

Inductive sem_array_init_helper (ge : genv) : Memory.mem -> Values.block -> ptrofs -> list value -> type -> Memory.mem -> Prop :=
| sem_allocate_array_elm_nil : forall m loc ofs t,
                               sem_array_init_helper ge m loc ofs nil t m
| sem_allocate_array_elm : forall m loc ofs v vs t m' m'',
                           assign_addr ge t m loc ofs Full v m' v ->
                           sem_array_init_helper ge m' loc
                             (Ptrofs.add ofs (Ptrofs.repr (sizeof_type ge.(genv_cenv) t))) vs t m'' ->
                           sem_array_init_helper ge m loc ofs (v :: vs) t m''
| sem_allocate_array_unit : forall m loc ofs vs final,
                           sem_array_init_helper ge m loc ofs vs Utype final ->
                           sem_array_init_helper ge m loc ofs (Vunit :: vs) Utype final.

Inductive sem_array_init (ge : genv) : store_context -> ident -> type -> list value -> vmap -> Memory.mem ->
                           vmap -> Memory.mem -> store_context -> Prop :=
| sem_allocate_array : forall Sigma vm arr t aty len a vs loc m vm' m' m'' Sigma',
                       alloc_variables ge Sigma vm m ((arr, t) :: nil) vm' m' Sigma' ->
                       vm' ! arr = Some (loc, t) ->
                       t = Atype aty len a ->
                       len = Z.of_nat (List.length vs) ->
                       sem_array_init_helper ge m' loc Ptrofs.zero vs aty m'' ->
                       sem_array_init ge Sigma arr t vs vm m vm' m'' Sigma'.
          
(* Function parameters are immutable authentic code bindings. Other parameters
   retain the existing allocation/initialization semantics. No code block is
   entered into the mutable store context merely because it is an argument. *)
Inductive function_parameter_partition (ge : genv) :
    list (ident * type) -> list value -> vmap -> list (ident * type) -> list value -> Prop :=
| function_partition_nil :
    function_parameter_partition ge nil nil empty_vmap nil nil
| function_partition_code : forall id args effects result variadic params values
    b fn codes data data_values,
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
    type_of_function fn = Ftype args effects result variadic ->
    function_parameter_partition ge params values codes data data_values ->
    function_parameter_partition ge ((id, Ftype args effects result variadic) :: params)
      (Vloc b Ptrofs.zero :: values)
      (PTree.set id (b, Ftype args effects result variadic) codes) data data_values
| function_partition_data : forall id ty params v values codes data data_values,
    is_funtype ty = false ->
    function_parameter_partition ge params values codes data data_values ->
    function_parameter_partition ge ((id, ty) :: params) (v :: values)
      codes ((id, ty) :: data) (v :: data_values).

Definition has_function_parameter (params : list (ident * type)) : Prop :=
  exists id args effects result variadic,
    List.In (id, Ftype args effects result variadic) params.

Section Big_Step_Semantics.

Variable (ge : genv).

(* Big step semantics without lv, rv, or context *) 
Inductive bsem_expr : program -> vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> value -> Prop := 
| bsem_value : forall p vm m v t,
               well_formed_value v t ->
               bsem_expr p vm m (Val v t) m vm v
| bsem_lvar : forall p vm m x t l v,
              vm!x = Some (l, t) -> 
              deref_addr t m l Ptrofs.zero Full v ->
              bsem_expr p vm m (Var x t) m vm v
| bsem_gbvar : forall p vm m x t l v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr t m l Ptrofs.zero Full v ->
               bsem_expr p vm m (Var x t) m vm v
| bsem_consti : forall p vm m i t,
                bsem_expr p vm m (Const (ConsInt i) t) m vm (Vint i)
| bsem_constl : forall p vm m i t, 
                bsem_expr p vm m (Const (ConsLong i) t) m vm (Vint64 i)
| bsem_constu : forall p vm m,
                bsem_expr p vm m (Const (ConsUnit) Utype) m vm (Vunit)
| bsem_appr : forall p vm1 vm_callee m1 e es t l fd m2 m3 m4 m5 m6 vs rv Sigma ,
              (* head: evaluate the function expression to a pointer/location *)
              bsem_expr p vm1 m1 e m2 vm1 (Vloc l Ptrofs.zero) ->
              Genv.find_funct ge (trans_bvalue_cvalue (Vloc l Ptrofs.zero))  = Some (Internal fd) ->
              BeePL.type_of_fundef (Internal fd) =
                Ftype (typeof_exprs es) (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) (get_v_fundef (Internal fd)) ->
              list_norepet (fd.(fn_args) ++ fd.(BeePL.fn_vars)) ->
              (* allocate callee locals/args: produce vm_callee *)
              alloc_variables ge empty_context empty_vmap m2 (fd.(fn_args) ++ fd.(BeePL.fn_vars)) vm_callee m3 Sigma ->
              (* evaluate arguments in the CALLER env *)
              bsem_exprs p vm1 m3 es m4 vm1 vs ->
              typeof_values vs (unzip2 fd.(fn_args)) ->
              (* bind parameters in the CALLEE env *)
              bind_variables ge vm_callee m4 fd.(fn_args) vs m5 ->
              (* execute the callee body under CALLEE env *)
              bsem_expr p vm_callee m5 fd.(BeePL.fn_body) m6 vm_callee rv ->
              typeof_value rv (get_rt_fundef (Internal fd)) ->
              t = (get_rt_fundef (Internal fd)) ->
              (* return to the caller: env is vm1 again *)
              bsem_expr p vm1 m1 (App e es t) m6 vm1 rv
| bsem_ref : forall bge p vm m e m' ml m'' v l a t,
             bsem_expr p vm m e m' vm v ->
             Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (Vtype t)) = ml ->
             assign_addr bge (Vtype t) ml.1 ml.2 Ptrofs.zero Full v m'' v -> 
             bsem_expr p vm m (Prim Ref [:: e] (Ptrtype (Reftype (Bprim t) a))) m'' vm (Vloc l Ptrofs.zero)
| bsem_deref : forall p vm m e m' l ofs v,
               bsem_expr p vm m e m' vm (Vloc l ofs) ->
               deref_addr (typeof_expr e) m' l ofs Full v ->
               bsem_expr p vm m (Prim Deref (e :: nil) (typeof_expr e)) m' vm v
| bsem_massgn : forall p vm m e1 m' l ofs e2 m'' v v' pt ct1 ct2 m''',  
                bsem_expr p vm m e1 m' vm (Vloc l ofs) ->
                bsem_expr p vm m' e2 m'' vm v ->
                transBeePL_type (typeof_expr e1) = ct1  ->
                transBeePL_type (typeof_expr e2) = ct2  ->
                typeof_expr e1 = Ptrtype pt ->
                typeof_expr e2 = get_data_type pt ->
                sem_cast (trans_bvalue_cvalue v) ct2 ct1 m = Some (trans_bvalue_cvalue v') ->
                assign_addr ge (typeof_expr e1) m'' l ofs Full v' m''' v' -> 
                chunk_for_volatile_type (transBeePL_type (typeof_expr e1)) Full = None ->
                bsem_expr p vm m (Prim Massgn (e1 :: e2 :: nil) (typeof_expr e1)) m''' vm v'
| bsem_uop : forall p vm m e v uop m' v' ct v'',
             bsem_expr p vm m e m' vm v ->
             transBeePL_type (typeof_expr e) = ct ->
             sem_unary_operation uop (trans_bvalue_cvalue v) ct m' = Some v' ->
             trans_cvalue_bvalue v' = OK v'' ->
             bsem_expr p vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm v''
| bsem_bop_unsafe : forall p vm m e1 e2 v1 v2 bop s m' m'' zv,
                    bsem_expr p vm m e1 m' vm v1 ->
                    bsem_expr p vm m' e2 m'' vm v2 ->
                    arithmetic_signedness_of_type (typeof_expr e1) = Some s ->
                    check_unsafe_op bop s v1 v2 = true ->
                    return_bzero (typeof_expr e1) = OK zv ->
                    bsem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm zv
| bsem_bop_safe : forall p cenv vm m e1 e2 v1 v2 bop s m' m'' ct1 ct2 v v',
                  bsem_expr p vm m e1 m' vm v1 ->
                  bsem_expr p vm m' e2 m'' vm v2 ->
                  arithmetic_signedness_of_type (typeof_expr e1) = Some s ->
                  check_unsafe_op bop s v1 v2 = false ->
                  transBeePL_type (typeof_expr e1) = ct1 ->
                  transBeePL_type (typeof_expr e2) = ct2 ->
                  sem_binary_operation cenv bop (trans_bvalue_cvalue v1) ct1 
                                           (trans_bvalue_cvalue v2) ct2 m'' = Some v ->
                  trans_cvalue_bvalue v = OK v' ->
                  bsem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) (typeof_expr e1)) m'' vm v'
| ssem_bcast : forall p vm vm' m e m' v t2 v' v'',
               bsem_expr p vm m e m' vm' v ->
               sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e)) (transBeePL_type t2) m' = Some v' ->
               decode_memory_value t2 v' = OK v'' ->
               bsem_expr p vm m (Prim (Cast t2) (e:: nil) t2) m' vm' v''
| bsem_bind_subst : forall bge p vm m x e1 m' m'' m''' v e2 l v' tx,
                    bsem_expr p vm m e1 m' vm v -> 
                    not (x =? Ctypesdefs.ident_of_string "_")%positive ->
                    vm!x = Some (l, tx) ->
                    chunk_for_volatile_type (transBeePL_type tx) Full = None ->
                    Cop.sem_cast (trans_bvalue_cvalue v) (transBeePL_type (typeof_expr e1))
                      (transBeePL_type tx) m' = Some (trans_bvalue_cvalue v) ->
                    assign_addr bge tx m' l Ptrofs.zero Full v m'' v -> 
                    (* vm <- (x, v) ==> vm'; [e2]vm'--> v'*)
                    (*SubstE x (Val v (typeof_expr e1)) e2 e2' ->*)
                    bsem_expr p vm m'' e2 m''' vm v' ->
                    bsem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m''' vm v'
| bsem_bind_no_subst : forall p vm m x e1 m' m'' v e2 v' tx,
                       bsem_expr p vm m e1 m' vm v -> 
                       (x =? Ctypesdefs.ident_of_string "_")%positive ->
                       bsem_expr p vm m' e2 m'' vm v' ->
                       bsem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m'' vm v'
| bsem_ctrue : forall p vm m e1 e2 e3 t  m' vb ct1 v' v v'' m'', 
               bsem_expr p vm m e1 m' vm vb -> 
               transBeePL_type (typeof_expr e1) = ct1 ->
               bool_val (trans_bvalue_cvalue vb) ct1 m' = Some true ->
               bsem_expr p vm m' e2 m'' vm v' ->
               Cop.sem_cast (trans_bvalue_cvalue v') (transBeePL_type (typeof_expr e2)) (transBeePL_type t) m'' = Some v'' ->
               trans_cvalue_bvalue v'' = OK v ->
               bsem_expr p vm m (Cond e1 e2 e3 t) m'' vm v
| bsem_cfalse : forall p vm m e1 e2 e3 t m' vb ct1 v' v v'' m'', 
                bsem_expr p vm m e1 m' vm vb -> 
                transBeePL_type (typeof_expr e1) = ct1 ->
                bool_val (trans_bvalue_cvalue vb) ct1 m' = Some false ->
                bsem_expr p vm m' e3 m'' vm v' ->
                Cop.sem_cast (trans_bvalue_cvalue v') (transBeePL_type (typeof_expr e3)) (transBeePL_type t) m'' = Some v'' ->
                trans_cvalue_bvalue v'' = OK v ->
                bsem_expr p vm m (Cond e1 e2 e3 t) m'' vm v
| bsem_ut : forall p vm m, 
            bsem_expr p vm m (Unit Utype) m vm Vunit
| bsem_adr : forall p vm m l ofs t,
             bsem_expr p vm m (Addr l ofs t) m vm (Vloc l.(lname) ofs)
(*| bsem_eapp : forall p vm m es vm' m' m'' vs ef cef vres bv ts ty t,
              bsem_exprs p vm m es m' vm' vs ->
              befunction_to_cefunction ef = cef ->
              external_call cef ge (trans_bvalues_cvalues vs) m' t vres m'' ->
              trans_cvalue_bvalue vres = OK bv ->
              bsem_expr p vm m (BeePL.Eapp ef ts es ty) m'' vm' bv*)
| bsem_screate : forall p sid ids es vm1 m1 vm2 m2 allocated initialized vs loc sa t,
                 structure_result_type sid sa t ->
                 bsem_exprs p vm1 m1 es m2 vm2 vs ->
                 Mem.alloc m2 0 (sizeof_type ge.(genv_cenv) (Stype sid sa)) = (allocated, loc) ->
                 sem_allocate_fields ge loc Ptrofs.zero sid ids vs (map typeof_expr es) allocated initialized ->
                 bsem_expr p vm1 m1 (Sinit sid ids es t)
                   initialized vm2 (Vloc loc Ptrofs.zero)
| bsem_sfield : forall p b ofs co delta bf f vm m vm' m' e t sid sa v,
                bsem_expr p vm m e m' vm' (Vloc b ofs) ->
                typeof_expr e = (Ptrtype (Reftype (Bstruct sid sa) noattr)) ->
                ge.(genv_cenv)!sid = Some co ->
                field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                deref_addr t m' b (Ptrofs.add ofs (Ptrofs.repr delta)) bf v ->
                bsem_expr p vm m (Sfield e f t)  
                               m' vm' v
| bsem_for : forall p e1 e2 d e3 lo hi n vm m vm' m' vm'' m'' vm''' m''' t v',
             bsem_expr p vm m e1 m' vm' lo ->
             bsem_expr p vm' m' e2 m'' vm'' hi ->
             compute_loop_iterations d (typeof_expr e1) lo hi = OK n ->
             bsem_bfor p n vm'' m'' e3 m''' vm''' v' ->
             bsem_expr p vm m (For e1 e2 d e3 t) m''' vm''' v'
| bsem_none : forall p m vm t,
              bsem_expr p vm m (Enone t) m vm (Voption None)
| bsem_some : forall p m vm t e vm' m' v,
              bsem_expr p vm m e m' vm' v ->
              bsem_expr p vm m (Esome e t) m' vm' (Voption (Some v))
(* Option elimination evaluates only the selected branch, after the scrutinee.
   A Some binder receives the non-null pointer itself, not its pointee. *)
| bsem_match_none : forall p m vm t e x enone esome vm' m' vm'' m'' result,
                    bsem_expr p vm m e m' vm' (Voption None) ->
                    bsem_expr p vm' m' enone m'' vm'' result ->
                    bsem_expr p vm m
                      (Match e (Pnone :: Psome x :: nil) (enone :: esome :: nil) t)
                      m'' vm'' result
| bsem_match_some : forall p m vm t e pt value x enone esome vm' m' vm'' m'' result,
                    typeof_expr e = Ptrtype (Otype pt) ->
                    bsem_expr p vm m e m' vm' (Voption (Some value)) ->
                    bsem_expr p vm' m' (subst x (Val value (Ptrtype pt)) esome) m'' vm'' result ->
                    bsem_expr p vm m
                      (Match e (Pnone :: Psome x :: nil) (enone :: esome :: nil) t)
                      m'' vm'' result
| bsem_ainit : forall Sigma p vm m m' vm' vs arr t es loc vm'' m'' Sigma', 
               bsem_exprs p vm m es m' vm' vs ->
               sem_array_init ge Sigma arr t vs vm' m' vm'' m'' Sigma' ->
               vm'' ! arr = Some (loc, t) ->
               bsem_expr p vm m (Ainit arr t es t) m'' vm' (Vloc loc (Ptrofs.repr 0))
| bsem_array_read : forall p vm m e m' vm' b base elem len a n v,
                 bsem_expr p vm m e m' vm' (Vloc b base) ->
                 typeof_expr e = Atype elem len a ->
                 PeanoNat.Nat.lt n (Z.to_nat len) ->
                 deref_addr elem m' b (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) Full v ->
                 bsem_expr p vm m (Prim (ArrayRead n) (e :: nil) elem) m' vm' v
| bsem_aaccess : forall p vm m arr t n loc aty len a v,
                 vm ! arr = Some (loc, t) ->
                 t = Atype aty len a ->
                 PeanoNat.Nat.lt n (Z.to_nat len) ->
                 deref_addr aty m loc (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) aty)) Full v ->
                 bsem_expr p vm m (Aaccess arr t n aty) m vm v
| bsem_aaccess_global : forall p vm m arr elem len a n b v,
                 vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
                 PeanoNat.Nat.lt n (Z.to_nat len) ->
                 deref_addr elem m b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) Full v ->
                 bsem_expr p vm m (Aaccess arr (Atype elem len a) n elem) m vm v
| bsem_lvar_array : forall p vm m x elem len a b,
              vm ! x = Some (b, Atype elem len a) ->
              bsem_expr p vm m (Var x (Atype elem len a)) m vm (Vloc b Ptrofs.zero)
| bsem_gbvar_array : forall p vm m x elem len a b,
              vm ! x = None -> Genv.find_symbol ge x = Some b ->
              bsem_expr p vm m (Var x (Atype elem len a)) m vm (Vloc b Ptrofs.zero)
| bsem_call_frame : forall p caller callee m body t m' callee' v,
              bsem_expr p callee m body m' callee' v ->
              bsem_expr p caller m (CallFrame callee body t) m' caller v
(* fix me : add semantics for hexpr *)
| bsem_global_function : forall p vm m x b fn args effects result variadic,
    vm ! x = None ->
    Genv.find_symbol ge x = Some b ->
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
    type_of_function fn = Ftype args effects result variadic ->
    bsem_expr p vm m (Var x (Ftype args effects result variadic)) m vm
      (Vloc b Ptrofs.zero)
| bsem_match_none_first_some : forall p m vm t e x esome enone vm' m' vm'' m'' result,
                    bsem_expr p vm m e m' vm' (Voption None) ->
                    bsem_expr p vm' m' enone m'' vm'' result ->
                    bsem_expr p vm m
                      (Match e (Psome x :: Pnone :: nil) (esome :: enone :: nil) t)
                      m'' vm'' result
| bsem_match_some_first : forall p m vm t e pt value x esome enone vm' m' vm'' m'' result,
                    typeof_expr e = Ptrtype (Otype pt) ->
                    bsem_expr p vm m e m' vm' (Voption (Some value)) ->
                    bsem_expr p vm' m' (subst x (Val value (Ptrtype pt)) esome) m'' vm'' result ->
                    bsem_expr p vm m
                      (Match e (Psome x :: Pnone :: nil) (esome :: enone :: nil) t)
                      m'' vm'' result

(* Unit bindings carry no stored payload, so evaluating them does not read memory. *)
| bsem_lvar_unit : forall p vm m x b,
    PTree.get x vm = Some (b, Utype) ->
    bsem_expr p vm m (Var x Utype) m vm Vunit
| bsem_gbvar_unit : forall p vm m x b,
    PTree.get x vm = None -> Genv.find_symbol ge x = Some b ->
    bsem_expr p vm m (Var x Utype) m vm Vunit

(* Aggregate dereference produces its address representation after the operand
   has evaluated. The footprint is checked without pretending it is a scalar. *)
| bsem_deref_aggregate : forall p vm m e m' vm' b base basic attr,
    bsem_expr p vm m e m' vm' (Vloc b base) ->
    typeof_expr e = Ptrtype (Reftype basic attr) ->
    aggregate_readable ge.(genv_cenv) m' b base (construct_type_btype basic) ->
    bsem_expr p vm m (Prim Deref (e :: nil) (construct_type_btype basic))
      m' vm' (Vloc b base)

(* Aggregate references allocate a distinct object and copy its representation. *)
| bsem_ref_aggregate : forall p vm m e evaluated vm' src base basic attr allocated fresh final,
    bsem_expr p vm m e evaluated vm' (Vloc src base) ->
    typeof_expr e = construct_type_btype basic ->
    is_aggregate_type (construct_type_btype basic) = true ->
    Mem.alloc evaluated 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) =
      (allocated, fresh) ->
    assign_addr ge (construct_type_btype basic) allocated fresh Ptrofs.zero Full
      (Vloc src base) final (Vloc src base) ->
    bsem_expr p vm m (Prim Ref [:: e] (Ptrtype (Reftype basic attr)))
      final vm' (Vloc fresh Ptrofs.zero)

| bsem_array_read_aggregate : forall p vm m e m' vm' b base elem len attr n,
    bsem_expr p vm m e m' vm' (Vloc b base) ->
    typeof_expr e = Atype elem len attr ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Ptrofs.unsigned base + Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m' b
      (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem ->
    bsem_expr p vm m (Prim (ArrayRead n) [:: e] elem) m' vm'
      (Vloc b (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))))
| bsem_aaccess_aggregate : forall p vm m arr b elem len attr n,
    vm ! arr = Some (b, Atype elem len attr) ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m b
      (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) elem ->
    bsem_expr p vm m (Aaccess arr (Atype elem len attr) n elem) m vm
      (Vloc b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)))
| bsem_aaccess_global_aggregate : forall p vm m arr b elem len attr n,
    vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m b
      (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) elem ->
    bsem_expr p vm m (Aaccess arr (Atype elem len attr) n elem) m vm
      (Vloc b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)))

| bsem_array_read_unit : forall p vm m e m' vm' b base len attr n,
    bsem_expr p vm m e m' vm' (Vloc b base) ->
    typeof_expr e = Atype Utype len attr ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m' b base (Atype Utype len attr) ->
    bsem_expr p vm m (Prim (ArrayRead n) [:: e] Utype) m' vm' Vunit
| bsem_aaccess_unit : forall p vm m arr b len attr n,
    vm ! arr = Some (b, Atype Utype len attr) ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m b Ptrofs.zero (Atype Utype len attr) ->
    bsem_expr p vm m (Aaccess arr (Atype Utype len attr) n Utype) m vm Vunit
| bsem_aaccess_global_unit : forall p vm m arr b len attr n,
    vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m b Ptrofs.zero (Atype Utype len attr) ->
    bsem_expr p vm m (Aaccess arr (Atype Utype len attr) n Utype) m vm Vunit

| bsem_loop_frame : forall p vm m remaining template active m' vm' m'' vm'',
    bsem_expr p vm m active m' vm' Vunit ->
    bsem_bfor p (Z.of_nat remaining) vm' m' template m'' vm'' Vunit ->
    bsem_expr p vm m (LoopFrame remaining template active) m'' vm'' Vunit

| bsem_local_function : forall p vm m x b fn args effects result variadic,
    vm ! x = Some (b, Ftype args effects result variadic) ->
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
    type_of_function fn = Ftype args effects result variadic ->
    bsem_expr p vm m (Var x (Ftype args effects result variadic)) m vm (Vloc b Ptrofs.zero)
| bsem_app_code_parameters : forall p caller m e es t b fd function_memory argument_memory
    caller' values codes data data_values callee allocated initialized final final_callee rv Sigma Sigma',
    bsem_expr p caller m e function_memory caller' (Vloc b Ptrofs.zero) ->
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fd) ->
    type_of_function fd = Ftype (typeof_exprs es) (fn_effect fd) (fn_return fd) (get_v_fundef (Internal fd)) ->
    t = fn_return fd ->
    list_norepet (unzip1 (fn_args fd)) -> has_function_parameter (fn_args fd) ->
    bsem_exprs p caller' function_memory es argument_memory caller' values ->
    function_parameter_partition ge (fn_args fd) values codes data data_values ->
    alloc_variables ge Sigma codes argument_memory data callee allocated Sigma' ->
    bind_variables ge callee allocated data data_values initialized ->
    bsem_expr p callee initialized (fn_body fd) final final_callee rv ->
    bsem_expr p caller m (App e es t) final caller' rv

| bsem_constb : forall p vm m b,
    bsem_expr p vm m (Const (ConsBool b) (Vtype Tbool)) m vm (Vbool b)

| bsem_lvar_struct : forall p vm m x id attr b,
    vm ! x = Some (b, Stype id attr) ->
    bsem_expr p vm m (Var x (Stype id attr)) m vm (Vloc b Ptrofs.zero)
| bsem_gbvar_struct : forall p vm m x id attr b,
    vm ! x = None -> Genv.find_symbol ge x = Some b ->
    bsem_expr p vm m (Var x (Stype id attr)) m vm (Vloc b Ptrofs.zero)

with bsem_exprs : program -> vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list value -> Prop :=
| bsem_nil : forall p vm m,
             bsem_exprs p vm m nil m vm nil
| bsem_cons : forall p vm m m' m'' v vs e es vm' vm'',
              bsem_expr p vm m e m' vm' v ->
              bsem_exprs p vm' m' es m'' vm'' vs ->
              bsem_exprs p vm m (e :: es) m'' vm'' (v :: vs)
with bsem_bfor : program -> Z -> vmap -> Memory.mem -> expr -> Memory.mem -> vmap -> value -> Prop :=
| bsem_for_nil : forall p vm m e,
                 bsem_bfor p (Z.of_nat O) vm m e m vm Vunit
| bsem_for_one : forall p n vm m e m' vm' vm'' m'' v v',
                 bsem_expr p vm m e m' vm' v ->
                 bsem_bfor p (Z.of_nat n) vm' m' e m'' vm'' v' ->
                 bsem_bfor p (Z.of_nat (S n)) vm m e m'' vm'' v'.

End Big_Step_Semantics.


Scheme bsem_expr_ind_mut := Induction for bsem_expr Sort Prop
  with bsem_exprs_ind_mut := Induction for bsem_exprs Sort Prop.
Combined Scheme bsem_exprs_bsem_expr_ind_mut from bsem_exprs_ind_mut, bsem_expr_ind_mut.

Definition extract_value_expr (e : BeePL.expr) : list value :=
match e with 
| Val v t => [:: v]
| _ => nil
end.

Fixpoint extract_values_exprs (es : list BeePL.expr) : list value := 
match es with 
| nil => nil
| e :: es => extract_value_expr e ++ extract_values_exprs es 
end.

(* C represents booleans as integers; BeePL has a distinct boolean value. *)
Definition decode_boolean_result (v : Values.val) : res value :=
  match v with
  | Values.Vint i => OK (Vbool (negb (Int.eq i Int.zero)))
  | _ => Error (msg "Expected a boolean operator result")
  end.

Definition decode_unary_result (op : Cop.unary_operation) (v : Values.val) : res value :=
  match op with
  | Cop.Onotbool => decode_boolean_result v
  | _ => trans_cvalue_bvalue v
  end.

Definition binary_result_type (op : Cop.binary_operation) (operand_type : type) : type :=
  match op with
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => Vtype Tbool
  | _ => operand_type
  end.

Definition decode_binary_result (op : Cop.binary_operation) (v : Values.val) : res value :=
  match op with
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => decode_boolean_result v
  | _ => trans_cvalue_bvalue v
  end.

Definition is_value (e : BeePL.expr) : bool :=
match e with
| Val _ _ => true
| _ => false
end.

Fixpoint is_values (es : list BeePL.expr) : bool :=
match es with
| nil => true
| e :: es => is_value e && is_values es
end.


Section Small_Step_Semantics.

Variable (ge : genv).

Inductive ssem_expr : program -> vmap -> Memory.mem -> BeePL.expr -> Memory.mem -> vmap -> BeePL.expr -> Prop :=
(*| ssem_value : forall p vm m v t,
               well_formed_value v t ->
               ssem_expr p vm m (Val v t) m vm (Val v t)*)
| ssem_lvar : forall p vm m x t l v,
              vm!x = Some (l, t) -> 
              deref_addr t m l Ptrofs.zero Full v ->
              ssem_expr p vm m (Var x t) m vm (Val v t)
| ssem_gbvar : forall p vm m x t l v,
               vm!x = None ->
               Genv.find_symbol ge x = Some l -> 
               deref_addr t m l Ptrofs.zero Full v ->
               ssem_expr p vm m (Var x t) m vm (Val v t)
| ssem_lvar_array : forall p vm m x elem len a b,
              vm ! x = Some (b, Atype elem len a) ->
              ssem_expr p vm m (Var x (Atype elem len a)) m vm
                (Val (Vloc b Ptrofs.zero) (Atype elem len a))
| ssem_gbvar_array : forall p vm m x elem len a b,
              vm ! x = None -> Genv.find_symbol ge x = Some b ->
              ssem_expr p vm m (Var x (Atype elem len a)) m vm
                (Val (Vloc b Ptrofs.zero) (Atype elem len a))
| ssem_consti : forall p vm m i t,
                ssem_expr p vm m (Const (ConsInt i) t) m vm (Val (Vint i) t)
| ssem_constl : forall p vm m i t, 
                ssem_expr p vm m (Const (ConsLong i) t) m vm (Val (Vint64 i) t)
| ssem_constu : forall p vm m,
                ssem_expr p vm m (Const (ConsUnit) Utype) m vm (Val (Vunit) Utype)
| ssem_app1 : forall p vm1 m1 e es t e' m2 vm2,
              ssem_expr p vm1 m1 e m2 vm2 e' ->
              ssem_expr p vm1 m1 (App e es t) m2 vm2 (App e' es t)
| ssem_app2 : forall p vm1 m1 l o es vt t es' m2 vm2,
              is_values es = false ->
              ssem_exprs p vm1 m1 es m2 vm2 es' ->
              ssem_expr p vm1 m1 (App (Val (Vloc l o) vt) es t) m2 vm2 
                (App (Val (Vloc l o) vt) es' t)
| ssem_app3 : forall Sigma Sigma' p caller callee m es t l o fd allocated initialized,
              Genv.find_funct ge (trans_bvalue_cvalue (Vloc l o)) = Some (Internal fd) ->
              t = get_rt_fundef (Internal fd) ->
              List.Forall (fun e => exists v ty, e = Val v ty) es ->
              typeof_exprs es = unzip2 fd.(fn_args) ->
              list_norepet (unzip1 fd.(fn_args)) ->
              (* Source locals are introduced lexically by substitution. Only
                 parameters belong to the initial callee lookup map. *)
              alloc_variables ge Sigma empty_vmap m fd.(fn_args) callee allocated Sigma' ->
              bind_variables ge callee allocated fd.(fn_args) (extract_values_exprs es) initialized ->
              ssem_expr p caller m
                (App (Val (Vloc l o) (Ftype (typeof_exprs es)
                  (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd))
                  (get_v_fundef (Internal fd)))) es t)
                initialized caller (CallFrame callee fd.(fn_body) t)
| ssem_ref1 : forall p vm m e m' vm' e' bt a,
              ssem_expr p vm m e m' vm' e' ->
              ssem_expr p vm m (Prim Ref [:: e] (Ptrtype (Reftype bt a))) m' vm' 
                             (Prim Ref [:: e'] (Ptrtype (Reftype bt a)))
| ssem_ref2 : forall p vm m ml m' chunk v l bt a Sigma Sigma',
              Mem.alloc m 0 (sizeof_type p.(prog_comp_env) (construct_type_btype bt)) = ml ->
              chunk_of_type (construct_type_btype bt) = Some chunk ->
              Mem.storev (transl_bchunk_cchunk chunk) ml.1 (trans_bvalue_cvalue (Vloc ml.2 Ptrofs.zero)) (trans_bvalue_cvalue v) = Some m' ->
              (*assign_addr bge (construct_type_btype bt) ml.1 ml.2 Ptrofs.zero Full v m'' v -> *)
              PTree.set l (Ptrtype (Reftype bt a)) Sigma = Sigma' ->
              ssem_expr p vm m (Prim Ref [:: (Val v (construct_type_btype bt))] (Ptrtype (Reftype bt a))) m' vm
                             (Val (Vloc ml.2 Ptrofs.zero) (Ptrtype (Reftype bt a)))
| ssem_deref1 : forall p vm m e t m' vm' e',
                ssem_expr p vm m e m' vm' e' ->
                ssem_expr p vm m (Prim Deref (e :: nil) t) m' vm' 
                                 (Prim Deref (e' :: nil) t)
| ssem_deref2 : forall p vm m l ofs v t,
                deref_addr (get_data_type t) m l ofs Full v ->
                ssem_expr p vm m (Prim Deref [:: Val (Vloc l ofs) (Ptrtype t)] (get_data_type t)) m vm 
                               (Val v (get_data_type t))
| ssem_massgn1 : forall p vm m e1 e2 m' vm' e1',  
                 ssem_expr p vm m e1 m' vm' e1' ->
                 ssem_expr p vm m (Prim Massgn (e1 :: e2 :: nil) Utype) m' vm' 
                                (Prim Massgn (e1' :: e2 :: nil) Utype)
| ssem_massgn2 : forall p vm m e2 e2' m' vm' l ofs t,  
                 ssem_expr p vm m e2  m' vm' e2' ->
                 ssem_expr p vm m (Prim Massgn ((Val (Vloc l ofs) (Ptrtype t)) :: e2 :: nil) Utype) m' vm' 
                                (Prim Massgn ((Val (Vloc l ofs) (Ptrtype t)) :: e2' :: nil) Utype)
| ssem_massgn3 : forall p vm m t m' l ofs v,
                 assign_addr ge (get_data_type t) m l ofs Full v m' v ->
                 ssem_expr p vm m (Prim Massgn (Val (Vloc l ofs) (Ptrtype t) ::  Val v (get_data_type t):: nil) Utype )
                                m' vm (Val Vunit Utype)
| ssem_uop1 : forall p vm m e e' uop vm' m',
              ssem_expr p vm m e m' vm' e' ->
              ssem_expr p vm m (Prim (Uop uop) (e :: nil) (typeof_expr e)) m' vm'
                             (Prim (Uop uop) (e' :: nil) (typeof_expr e))
| ssem_uop2 : forall p vm m t v uop v' ct v'',
             transBeePL_type t = ct ->
             sem_unary_operation uop (trans_bvalue_cvalue v) ct m = Some v' ->
             decode_unary_result uop v' = OK v'' ->
             ssem_expr p vm m (Prim (Uop uop) [:: (Val v t)] t) m vm (Val v'' t)
| ssem_bop1 : forall p vm m vm' m' bop e1 e2 e1' rt,
              ssem_expr p vm m e1 m' vm' e1' ->
              ssem_expr p vm m (Prim (Bop bop) (e1 :: e2 :: nil) rt) m' vm'
                             (Prim (Bop bop) (e1' :: e2 :: nil) rt)
| ssem_bop2 : forall p vm m vm' m' bop v1 t1 e2 e2' rt,
              ssem_expr p vm m e2 m' vm' e2' ->
              ssem_expr p vm m (Prim (Bop bop) (Val v1 t1 :: e2 :: nil) rt) m' vm'
                             (Prim (Bop bop) (Val v1 t1 :: e2' :: nil) rt)
| ssem_bop3_unsafe  : forall p vm m v1 v2 bop t ct s zv,
               transBeePL_type t = ct ->
               arithmetic_signedness_of_type t = Some s ->
               check_unsafe_op bop s v1 v2 = true ->
               return_bzero t = OK zv ->
               ssem_expr p vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) t) m vm (Val zv t) 
| ssem_bop3_safe  : forall p cenv vm m v1 v2 bop t v ct v' s,
                    transBeePL_type t = ct ->
                    arithmetic_signedness_of_type t = Some s ->
                    check_unsafe_op bop s v1 v2 = false ->
                    sem_binary_operation cenv bop (trans_bvalue_cvalue v1) ct 
                                            (trans_bvalue_cvalue v2) ct m = Some v ->
                    decode_binary_result bop v = OK v' ->
                    ssem_expr p vm m (Prim (Bop bop) (Val v1 t :: Val v2 t :: nil) (binary_result_type bop t))
                      m vm (Val v' (binary_result_type bop t))
| ssem_bool_eq : forall p vm m b1 b2,
    ssem_expr p vm m
      (Prim (Bop Cop.Oeq) (Val (Vbool b1) (Vtype Tbool) :: Val (Vbool b2) (Vtype Tbool) :: nil) (Vtype Tbool))
      m vm (Val (Vbool (Bool.eqb b1 b2)) (Vtype Tbool))
| ssem_bool_ne : forall p vm m b1 b2,
    ssem_expr p vm m
      (Prim (Bop Cop.One) (Val (Vbool b1) (Vtype Tbool) :: Val (Vbool b2) (Vtype Tbool) :: nil) (Vtype Tbool))
      m vm (Val (Vbool (negb (Bool.eqb b1 b2))) (Vtype Tbool))
| ssem_cast1 : forall p vm vm' m e e' m' t,
               ssem_expr p vm m e m' vm' e' ->
               ssem_expr p vm m (Prim (Cast t) (e :: nil) t) m' vm'
                                (Prim (Cast t) (e' :: nil) t)
| ssem_cast2 : forall p vm m v t1 t2 v' v'',
               sem_cast (trans_bvalue_cvalue v) (transBeePL_type t1) (transBeePL_type t2) m = Some v' ->
               decode_memory_value t2 v' = OK v'' ->
               ssem_expr p vm m (Prim (Cast t2) (Val v t1:: nil) t2) m vm (Val v'' t2)
(* fix me : add semantics for run primitive *)
| ssem_bind1 : forall p vm m x e1 e1' e2 vm' m' tx,
               ssem_expr p vm m e1 m' vm' e1' -> 
               ssem_expr p vm m (Bind x tx e1 e2 (typeof_expr e2)) m' vm' 
                              (Bind x tx e1' e2 (typeof_expr e2)) 
| ssem_bind2 : forall p vm m x v1 e2 tx e2',
               SubstE x (Val v1 tx) e2 e2' ->
               ssem_expr p vm m (Bind x tx (Val v1 tx) e2 (typeof_expr e2)) m vm e2' 
| ssem_cond : forall p vm m e1 e2 e3 vm' m' e1', 
              ssem_expr p vm m e1 m' vm' e1' -> 
              ssem_expr p vm m (Cond e1 e2 e3 (typeof_expr e2)) m' vm' (Cond e1' e2 e3 (typeof_expr e2))
| ssem_ctrue : forall p vm m e2 e3, 
               ssem_expr p vm m (Cond (Val (Vbool true) (Vtype Tbool)) e2 e3 (typeof_expr e2)) m vm e2
| ssem_cfalse : forall p vm m e2 e3,
                ssem_expr p vm m (Cond (Val (Vbool false) (Vtype Tbool)) e2 e3 (typeof_expr e3)) m vm e3
| ssem_ut : forall p vm m, 
            ssem_expr p vm m (Unit Utype) m vm (Val Vunit Utype)
| ssem_adr : forall p vm m l ofs t a,
             ssem_expr p vm m (Addr l ofs (Ptrtype (Reftype t a))) m vm (Val (Vloc l.(lname) ofs) (Ptrtype (Reftype t a)))
| ssem_sinit1 : forall p x ids t vm1 m1 es vm2 m2 es',
                  is_values es = false ->
                  ssem_exprs p vm1 m1 es m2 vm2 es' ->
                  ssem_expr p vm1 m1 (Sinit x ids es t) m2 vm2 (Sinit x ids es' t)
| ssem_sinit2 : forall p sid ids vm m allocated initialized vs loc sa t,
                  structure_result_type sid sa t ->
                  List.Forall (fun e => exists v t, e = Val v t) vs ->
                  Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (Stype sid sa)) = (allocated, loc) ->
                  sem_allocate_fields ge loc Ptrofs.zero sid ids (extract_values_exprs vs)
                    (typeof_exprs vs) allocated initialized ->
                  ssem_expr p vm m (Sinit sid ids vs t)
                    initialized vm (Val (Vloc loc Ptrofs.zero) t)
| ssem_sfield1 : forall p vm m e m' vm' e' f t, 
                 ssem_expr p vm m e m' vm' e' ->
                 ssem_expr p vm m (Sfield e f t) m' vm' (Sfield e' f t) 
| ssem_sfield2 : forall p b ofs co delta bf f vm m t sid sa v,
                 ge.(genv_cenv)!sid = Some co ->
                 field_offset (bcomposite_composite_env ge.(genv_cenv)) f (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                 deref_addr t m b (Ptrofs.add ofs (Ptrofs.repr delta)) bf v ->
                 ssem_expr p vm m (Sfield (Val (Vloc b ofs) (Ptrtype (Reftype (Bstruct sid sa) noattr))) f t)  
                               m vm (Val v t)
| ssem_sfield_struct : forall p b ofs co delta bf f vm m t sid sa v,
                 ge.(genv_cenv)!sid = Some co ->
                 field_offset (bcomposite_composite_env ge.(genv_cenv)) f
                   (bmembers_cmembers (co_members co)) = OK (delta, bf) ->
                 deref_addr t m b (Ptrofs.add ofs (Ptrofs.repr delta)) bf v ->
                 ssem_expr p vm m (Sfield (Val (Vloc b ofs) (Stype sid sa)) f t)
                   m vm (Val v t)
| ssem_sfield_aggregate : forall p vm m b ofs base_type f t result,
    aggregate_field_access ge.(genv_cenv) m b ofs base_type f t result ->
    ssem_expr p vm m (Sfield (Val (Vloc b ofs) base_type) f t)
      m vm (Val (Vloc b result) t)
| ssem_for1 : forall p vm m e1 e1' e2 vm' m' d e3 t,
              ssem_expr p vm m e1 m' vm' e1' ->
              ssem_expr p vm m (For e1 e2 d e3 t) m' vm' (For e1' e2 d e3 t) 
| ssem_for2 : forall p vm m v1 t1 e2 e2' vm' m' d e3 t,
              ssem_expr p vm m e2 m' vm' e2' ->
              ssem_expr p vm m (For (Val v1 t1) e2 d e3 t) m' vm' (For (Val v1 t1) e2' d e3 t)
(* Count computation enters an internal frame; one step never waits for
   completion of an iteration. Terminating summaries remain below. *)
| ssem_for3 : forall p vm m v1 t1 v2 t2 n d body,
    compute_loop_iterations d t1 v1 v2 = OK n ->
    ssem_expr p vm m (For (Val v1 t1) (Val v2 t2) d body Utype)
      m vm (match Z.to_nat n with
            | O => Val Vunit Utype
            | S remaining => LoopFrame remaining body body
            end)
| ssem_loop_frame_step : forall p vm m remaining template active m' vm' active',
    ssem_expr p vm m active m' vm' active' ->
    ssem_expr p vm m (LoopFrame remaining template active)
      m' vm' (LoopFrame remaining template active')
| ssem_loop_frame_done : forall p vm m template,
    ssem_expr p vm m (LoopFrame O template (Val Vunit Utype)) m vm (Val Vunit Utype)
| ssem_loop_frame_restart : forall p vm m remaining template,
    ssem_expr p vm m (LoopFrame (S remaining) template (Val Vunit Utype))
      m vm (LoopFrame remaining template template)
| ssem_none : forall p m vm t,
                ssem_expr p vm m (Enone t) m vm (Val (Voption None) t)
| ssem_some1 : forall p m vm t e vm' m' e',
               ssem_expr p vm m e m' vm' e' ->
               ssem_expr p vm m (Esome e t) m' vm' (Esome e' t)
| ssem_some2 : forall p m vm t v t',
               ssem_expr p vm m (Esome (Val v t) t') m vm (Val (Voption (Some v)) t')
| ssem_match_none1 : forall p m vm p1 p2 e1 e2 t' vm' m' e e',
                     ssem_expr p vm m e m' vm' e' ->
                     ssem_expr p vm m (Match e (p1 :: p2 :: nil) (e1 :: e2 :: nil) t') m' vm'
                      (Match e' (p1 :: p2 :: nil) (e1 :: e2 :: nil) t')
| ssem_match_none2 : forall p m vm t p1 p2 e1 e2 t',
                     ssem_expr p vm m (Match (Val (Voption None) t) (p1 :: p2 :: nil) (e1 :: e2 :: nil) t') m vm 
                      (if eq_pattern p1 Pnone then e1 else e2) 
| ssem_match_some : forall p m vm pt ve x enone esome t',
                    ssem_expr p vm m
                      (Match (Val (Voption (Some ve)) (Ptrtype (Otype pt)))
                        (Pnone :: Psome x :: nil) (enone :: esome :: nil) t') m vm
                      (subst x (Val ve (Ptrtype pt)) esome)
| ssem_match_some_first : forall p m vm pt ve x esome enone t',
                    ssem_expr p vm m
                      (Match (Val (Voption (Some ve)) (Ptrtype (Otype pt)))
                        (Psome x :: Pnone :: nil) (esome :: enone :: nil) t') m vm
                      (subst x (Val ve (Ptrtype pt)) esome)
| ssem_match_bytes : forall p vm m descriptor offset sid header rest fields yes no t m' body,
                     execute_packet_match ge.(genv_cenv) m descriptor offset sid header rest fields yes no =
                       OK (m', body) ->
                     ssem_expr p vm m
                       (Match (Val (Vloc descriptor offset) Bytes)
                         (Pbytes header (Stype sid noattr) fields :: Pbytes rest Bytes nil :: nil)
                         (yes :: no :: nil) t) m' vm body
| ssem_array_init1 : forall p vm m e es vm' m' e' arr t,
                     ssem_expr p vm m e m' vm' e' ->
                     ssem_expr p vm m (Ainit arr t (e :: es) t) m' vm' (Ainit arr t (e' :: es) t)
| ssem_array_init2 : forall p vm m v es vm' m' es' arr t aty,
                     is_values es = false ->
                     get_array_elm_ty t = OK aty ->
                     ssem_exprs p vm m es m' vm' es' ->
                     ssem_expr p vm m (Ainit arr t (Val v aty :: es) t) m' vm' (Ainit arr t (Val v aty :: es') t)
| ssem_array_init3 : forall Sigma Sigma' p vm m vs vm' m' arr t loc,
                     List.Forall (fun e => exists v ty, e = Val v ty) vs ->
                     sem_array_init ge Sigma arr t (extract_values_exprs vs) vm m vm' m' Sigma' ->
                     vm' ! arr = Some (loc, t) ->
                     ssem_expr p vm m (Ainit arr t vs t) m' vm (Val (Vloc loc Ptrofs.zero) t)
| ssem_array_read_context : forall p vm m e m' vm' e' n elem,
                      ssem_expr p vm m e m' vm' e' ->
                      ssem_expr p vm m (Prim (ArrayRead n) (e :: nil) elem)
                        m' vm' (Prim (ArrayRead n) (e' :: nil) elem)
| ssem_array_read_value : forall p vm m b base elem len a n v,
                      PeanoNat.Nat.lt n (Z.to_nat len) ->
                      deref_addr elem m b (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) Full v ->
                      ssem_expr p vm m
                        (Prim (ArrayRead n) (Val (Vloc b base) (Atype elem len a) :: nil) elem)
                        m vm (Val v elem)
| ssem_array_access : forall p vm m arr t n loc aty len a v,
                      vm ! arr = Some (loc, t) ->
                      t = Atype aty len a ->
                      PeanoNat.Nat.lt n (Z.to_nat len) ->
                      deref_addr aty m loc (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) aty)) Full v ->
                      ssem_expr p vm m (Aaccess arr t n aty) m vm (Val v aty)
| ssem_array_access_global : forall p vm m arr elem len a n b v,
                      vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
                      PeanoNat.Nat.lt n (Z.to_nat len) ->
                      deref_addr elem m b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) Full v ->
                      ssem_expr p vm m (Aaccess arr (Atype elem len a) n elem) m vm (Val v elem)
| ssem_call_frame_step : forall p caller callee m body t callee' m' body',
              ssem_expr p callee m body m' callee' body' ->
              ssem_expr p caller m (CallFrame callee body t)
                m' caller (CallFrame callee' body' t)
| ssem_call_frame_return : forall p caller callee m v t,
              ssem_expr p caller m (CallFrame callee (Val v t) t) m caller (Val v t)
| ssem_global_function : forall p vm m x b fn args effects result variadic,
    vm ! x = None ->
    Genv.find_symbol ge x = Some b ->
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
    type_of_function fn = Ftype args effects result variadic ->
    ssem_expr p vm m (Var x (Ftype args effects result variadic)) m vm
      (Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic))
| ssem_lvar_unit : forall p vm m x b,
    PTree.get x vm = Some (b, Utype) ->
    ssem_expr p vm m (Var x Utype) m vm (Val Vunit Utype)
| ssem_gbvar_unit : forall p vm m x b,
    PTree.get x vm = None -> Genv.find_symbol ge x = Some b ->
    ssem_expr p vm m (Var x Utype) m vm (Val Vunit Utype)

| ssem_deref_aggregate : forall p vm m b base basic attr,
    aggregate_readable ge.(genv_cenv) m b base (construct_type_btype basic) ->
    ssem_expr p vm m
      (Prim Deref [:: Val (Vloc b base) (Ptrtype (Reftype basic attr))]
        (construct_type_btype basic))
      m vm (Val (Vloc b base) (construct_type_btype basic))

| ssem_ref_aggregate : forall p vm m src base basic attr allocated fresh final,
    is_aggregate_type (construct_type_btype basic) = true ->
    Mem.alloc m 0 (sizeof_type ge.(genv_cenv) (construct_type_btype basic)) =
      (allocated, fresh) ->
    assign_addr ge (construct_type_btype basic) allocated fresh Ptrofs.zero Full
      (Vloc src base) final (Vloc src base) ->
    ssem_expr p vm m
      (Prim Ref [:: Val (Vloc src base) (construct_type_btype basic)]
        (Ptrtype (Reftype basic attr)))
      final vm (Val (Vloc fresh Ptrofs.zero) (Ptrtype (Reftype basic attr)))

| ssem_array_read_aggregate : forall p vm m b base elem len attr n,
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Ptrofs.unsigned base + Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m b
      (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem ->
    ssem_expr p vm m
      (Prim (ArrayRead n) [:: Val (Vloc b base) (Atype elem len attr)] elem) m vm
      (Val (Vloc b (Ptrofs.add base (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)))) elem)
| ssem_array_access_aggregate : forall p vm m arr b elem len attr n,
    vm ! arr = Some (b, Atype elem len attr) ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m b
      (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) elem ->
    ssem_expr p vm m (Aaccess arr (Atype elem len attr) n elem) m vm
      (Val (Vloc b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem)
| ssem_array_access_global_aggregate : forall p vm m arr b elem len attr n,
    vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    (Z.of_nat n * sizeof_type ge.(genv_cenv) elem <= Ptrofs.max_unsigned)%Z ->
    aggregate_readable ge.(genv_cenv) m b
      (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem)) elem ->
    ssem_expr p vm m (Aaccess arr (Atype elem len attr) n elem) m vm
      (Val (Vloc b (Ptrofs.repr (Z.of_nat n * sizeof_type ge.(genv_cenv) elem))) elem)

| ssem_array_read_unit : forall p vm m b base len attr n,
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m b base (Atype Utype len attr) ->
    ssem_expr p vm m
      (Prim (ArrayRead n) [:: Val (Vloc b base) (Atype Utype len attr)] Utype)
      m vm (Val Vunit Utype)
| ssem_array_access_unit : forall p vm m arr b len attr n,
    vm ! arr = Some (b, Atype Utype len attr) ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m b Ptrofs.zero (Atype Utype len attr) ->
    ssem_expr p vm m (Aaccess arr (Atype Utype len attr) n Utype) m vm (Val Vunit Utype)
| ssem_array_access_global_unit : forall p vm m arr b len attr n,
    vm ! arr = None -> Genv.find_symbol ge arr = Some b ->
    PeanoNat.Nat.lt n (Z.to_nat len) ->
    aggregate_readable ge.(genv_cenv) m b Ptrofs.zero (Atype Utype len attr) ->
    ssem_expr p vm m (Aaccess arr (Atype Utype len attr) n Utype) m vm (Val Vunit Utype)

| ssem_local_function : forall p vm m x b fn args effects result variadic,
    vm ! x = Some (b, Ftype args effects result variadic) ->
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b Ptrofs.zero)) = Some (Internal fn) ->
    type_of_function fn = Ftype args effects result variadic ->
    ssem_expr p vm m (Var x (Ftype args effects result variadic)) m vm
      (Val (Vloc b Ptrofs.zero) (Ftype args effects result variadic))
| ssem_app_code_parameters : forall Sigma Sigma' p caller m es t b offset fd codes data data_values
    callee allocated initialized,
    Genv.find_funct ge (trans_bvalue_cvalue (Vloc b offset)) = Some (Internal fd) ->
    t = get_rt_fundef (Internal fd) ->
    List.Forall (fun e => exists v ty, e = Val v ty) es ->
    typeof_exprs es = unzip2 (fn_args fd) ->
    list_norepet (unzip1 (fn_args fd)) -> has_function_parameter (fn_args fd) ->
    function_parameter_partition ge (fn_args fd) (extract_values_exprs es) codes data data_values ->
    alloc_variables ge Sigma codes m data callee allocated Sigma' ->
    bind_variables ge callee allocated data data_values initialized ->
    ssem_expr p caller m
      (App (Val (Vloc b offset) (Ftype (typeof_exprs es)
        (get_effect_fundef (Internal fd)) (get_rt_fundef (Internal fd)) (get_v_fundef (Internal fd)))) es t)
      initialized caller (CallFrame callee (fn_body fd) t)

| ssem_constb : forall p vm m b,
    ssem_expr p vm m (Const (ConsBool b) (Vtype Tbool)) m vm (Val (Vbool b) (Vtype Tbool))

| ssem_lvar_struct : forall p vm m x id attr b,
    vm ! x = Some (b, Stype id attr) ->
    ssem_expr p vm m (Var x (Stype id attr)) m vm (Val (Vloc b Ptrofs.zero) (Stype id attr))
| ssem_gbvar_struct : forall p vm m x id attr b,
    vm ! x = None -> Genv.find_symbol ge x = Some b ->
    ssem_expr p vm m (Var x (Stype id attr)) m vm (Val (Vloc b Ptrofs.zero) (Stype id attr))

with ssem_exprs : program -> vmap -> Memory.mem -> list BeePL.expr -> Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssem_nil : forall p vm m,
             ssem_exprs p vm m nil m vm nil
| ssem_cons1 : forall p vm m m' e e' es vm',
              ssem_expr p vm m e m' vm' e' ->
              ssem_exprs p vm m (e :: es) m' vm' (e' :: es)
| ssem_cons2 : forall p vm m es m' vm' v t vs,
               ssem_exprs p vm m es m' vm' vs ->
               ssem_exprs p vm m (Val v t :: es) m' vm' (Val v t :: vs)
with ssem_bfor : program -> Z -> vmap -> Memory.mem -> expr -> Memory.mem -> vmap -> expr -> Prop :=
| ssem_for_nil : forall p vm m e,
                 ssem_bfor p (Z.of_nat O) vm m e m vm (Val Vunit Utype)
| ssem_for_one : forall p n vm m e m' vm' vm'' m'' v',
                 ssem_loop_body p vm m e m' vm' ->
                 ssem_bfor p (Z.of_nat n) vm' m' e m'' vm'' v' ->
                 ssem_bfor p (Z.of_nat (S n)) vm m e m'' vm'' v'
with ssem_loop_body : program -> vmap -> Memory.mem -> expr -> Memory.mem -> vmap -> Prop :=
| ssem_loop_body_value : forall p vm m v t,
    ssem_loop_body p vm m (Val v t) m vm
| ssem_loop_body_step : forall p vm m e vm' m' e' vm'' m'',
    ssem_expr p vm m e m' vm' e' ->
    ssem_loop_body p vm' m' e' m'' vm'' ->
    ssem_loop_body p vm m e m'' vm''.

Scheme ssem_expr_ind_mut := Induction for ssem_expr Sort Prop
  with ssem_exprs_ind_mut := Induction for ssem_exprs Sort Prop.
Combined Scheme ssem_exprs_ssem_expr_ind_mut from ssem_exprs_ind_mut, ssem_expr_ind_mut.

End Small_Step_Semantics.

(** An expr is safe if it cannot get stuck by doing any transition - 
    Either it reaches a value or it takes step **)
Definition bsafe_expr (bge : genv) (p : program) (e : BeePL.expr) : Prop :=
forall v vm m vm' m', bsem_expr bge p vm m e vm' m' v.

Definition ssafe_expr (bge : genv) (p : program) (vm : vmap) (m : Memory.mem) (e : BeePL.expr) : Prop :=
is_value e \/ exists m' vm' e', ssem_expr bge p vm m e m' vm' e'.


Inductive ssem_closure : genv -> program -> vmap -> Memory.mem -> BeePL.expr -> nat -> 
                         Memory.mem -> vmap -> BeePL.expr -> Prop :=
| ssem_val : forall bge p vm m v t,
             ssem_closure bge p vm m (Val v t) 0%nat m vm (Val v t)
| ssem_one : forall bge p vm m e m' vm' e',
             ssem_expr bge p vm m e m' vm' e' ->
             ssem_closure bge p vm m e 1%nat m' vm' e'
| ssem_multi : forall bge p vm m e m' vm' e' n vm'' m'' e'',
               ssem_expr bge p vm m e m' vm' e' ->
               ssem_closure bge p vm' m' e' n m'' vm'' e'' ->
               ssem_closure bge p vm m e (n + 1) %nat m'' vm'' e''
with ssem_closures : genv -> program -> vmap -> Memory.mem -> list BeePL.expr -> nat ->
                     Memory.mem -> vmap -> list BeePL.expr -> Prop :=
| ssems_one : forall bge p vm m e m' vm' e',
              ssem_exprs bge p vm m e m' vm' e' ->
              ssem_closures bge p vm m e 1%nat m' vm' e'
| ssems_multi : forall bge p vm m e m' vm' e' n vm'' m'' e'',
                ssem_exprs bge p vm m e m' vm' e' ->
                ssem_closures bge p vm' m' e' n m'' vm'' e'' ->
                ssem_closures bge p vm m e (n + 1)%nat m'' vm'' e''.

          
(**
Reuse value domain 
What we want to do with respect to function calls? **)

(** int x = 3; 
    for (i = 0; i < x + 2) {
         body;  (** we should not decrement i **)
    } **)
(** verify at runtime if range is less than BPF_MAX_LOOPS **)

(** Types for integer variables : (int, range-interval)
    x + y 

             Gamma |- x : (t, rx)    Gamma |- y : (t, ry)
    -----------------------------------------------------------------
      Gamma |- x + y : (t, ((min(rx) + min(ry), max(rx) + max(ry))))


2+3 = 5

2 --> {2}
3 --> {3}
2+3 --> {5}


For var expr expr 

     Gamma |- n : int, rn  Gamma, (Gamma |- i : int, rn) |- e : (t, r), Gamma' 
                            Gamma' <= Gamma    
   ---------------------------------------------------------------------------------
   Gamma |- for (i = 0; i < n) e : (t


l := 4; 

|- l : ref, lr
|- 4 : int, {4}
{4} <= lr ***)


(*int uid; ---> *int


int x ----> int x *)


(* ref 0 ---> uid = 0; &uid where uid is fresh var *)

