Require Import BeePL_packet_schema_check.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping Coqlib.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs BeePL_notations.
Require Import BeePL_helper_functions.
Require Import BeePL_value_checker.
Require Import BeePL_storage_types BeePL_parameter_storage_check.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.

(***** Type checker for BeePL *****)

(* Type-checking of constants *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from constants *) 
Definition type_constant (c : BeePL_values.constant) : wtype :=
match c with 
| ConsInt i => Twint
| ConsLong i => Twlong
| ConsUnit => Twunit
| ConsBool b => Twbool
end.

(* Type-checking of values *)
(* We type check it with weak type: wtype because it is 
   hard to get size and signedness from values *) 
Definition type_value (v : value) : wtype :=
match v with 
| Vunit => Twunit
| Vbool b => Twbool
| Vint i => Twint
| Vint64 i => Twlong
| Vloc p ofs => Twptr
| Voption o => Twot
end.

Section Type_check_exprs. 

Variable type_check_expr : bcomposite_env -> ty_context -> store_context -> expr -> res (type * effect).

Fixpoint type_check_exprs (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (es : list expr) : res (list type * effect) :=
match es with 
| nil => OK (nil, nil)
| e :: es => do (te, efe) <- type_check_expr cenv Gamma Sigma e;
             do (tes, efes) <- type_check_exprs cenv Gamma Sigma es;
             OK (te :: tes, efe ++ efes)
end.

End Type_check_exprs. 

(* Look up the source field type directly. A round trip through C types loses
   BeePL's bytes and optional-pointer types. *)
(* The checker and declarative rules use the same nominal field lookup. *)
Definition type_of_bfield := source_member_type.

Fixpoint type_check_expr (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (e : expr) {struct e} : res (type * effect) :=
match e with 
| Val v t => if value_type_check cenv Sigma v t
             then OK (t, nil)
             else Error (msg "TYPE ERROR: Runtime value does not match its type or storage")
| Var x t => match (PTree.get x Gamma) with
             | Some t' => if (eq_type t t') then OK(t, nil) else Error (msg "TYPE ERROR: Var type does not match") 
             | None => Error (msg "TYPE ERROR: Variable not found")
             end
| Const c t =>
    match c, t with
    | ConsInt _, Vtype (Tint _ _ _)
    | ConsLong _, Vtype (Tlong _ _)
    | ConsBool _, Vtype Tbool
    | ConsUnit, Utype => OK (t, nil)
    | _, _ => Error (msg "TYPE ERROR: Constant annotation does not match its value")
    end
| App e es t => do (ft, efe) <- type_check_expr cenv Gamma Sigma e;
                do (ts, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
                match ft with 
                | Ftype ts1 ef rt1 v1 => if check_fun_ptr_fun ts1 ts && eq_type t rt1
                                         then OK (rt1, efe ++ ef ++ efs) 
                                         else Error (msg "TYPE ERROR: Function case does not match the inferred type") 
                | Ptrtype (Fptype ts1 ef rt1 v1) => if check_fun_ptr_fun ts1 ts && eq_type t rt1
                                                 then OK (rt1, efe ++ ef ++ efs) 
                                                 else Error (msg "TYPE ERROR: Function pointer case does not match the inferred type")

                | _ => Error (msg "TYPE ERROR: Not a function type")
                end
| Prim b es t => match b with 
                 | Ref => match es with 
                          | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                        match te with 
                                        | Vtype bt => if type_is_volatile (transBeePL_type (Vtype bt))
                                                        then Error (msg "TYPE ERROR: Volatile reference allocation is not supported")
                                                        else if eq_type t (Ptrtype (Reftype (Bprim bt) (attr_of_primitive_type bt)))
                                                        then OK (Ptrtype (Reftype (Bprim bt) (attr_of_primitive_type bt)), (ef ++ (Alloc :: nil)))
                                                        else Error (msg "TYPE ERROR: Reftype does not match the inferred type")
                                        | _ => Error (msg "TYPE ERROR: Only primitive types are allowed to be allocated in memory")
                                        end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Ref")
                          end
                 | Deref => match es with 
                            | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                          match te with 
                                          | Ptrtype pt => if eq_type t (get_data_type pt) 
                                                          then if (is_option_ptr_type pt == false) 
                                                               then if type_is_volatile (transBeePL_type (get_data_type pt))
                                                                    then Error (msg "TYPE ERROR: Volatile dereference is not supported")
                                                                    else OK (get_data_type pt, (ef ++ (Read :: nil)))
                                                               else Error (msg "Deref is not allowed on option type")
                                                          else Error (msg "Deref type does not match the inferred type")
                                          | _ => Error (msg "TYPE ERROR: Argument of dereferencing should be a ref type")
                                          end
                          |  _ => Error (msg "TYPE ERROR: Wrong number of arguments to Deref")
                          end
                 | Massgn => match es with 
                             | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                  match te1 with 
                                                  | Ptrtype pt => do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                                  if eq_type (get_data_type pt) te2 && eq_type t Utype
                                                                  then if (is_option_ptr_type pt == false)
                                                                       then if type_is_volatile (transBeePL_type (get_data_type pt))
                                                                            then Error (msg "TYPE ERROR: Volatile assignment is not supported")
                                                                            else OK (Utype, ef1 ++ ef2 ++ (Write :: nil))
                                                                       else Error (msg "Massgn is not allowed on option type")
                                                                  else Error (msg "Massgn source or result type mismatch")
                                                 | _ => Error (msg "TYPE ERROR: First argument of Massgn should be a reftype")
                                                 end
                            | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Massgn")
                            end                                                         
                 | Uop o => match o with 
                            | Cop.Onotbool => match es with 
                                              | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                            if is_primbool te && eq_type t te
                                                            then OK (te, ef)
                                                            else Error (msg "TYPE ERROR: Wrong argument type to negation bool operator, it expects bool as argument")
                                              | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                              end
                            | Cop.Onotint => match es with 
                                              | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                            if (is_primint te || is_primlong te) && eq_type t te
                                                            then OK (te, ef)
                                                            else Error (msg "TYPE ERROR: Wrong argument type to bitwise not operator, it expects int or long as argument")
                                              | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                              end
                            | Cop.Oneg => match es with 
                                          | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                                                        if (is_primint te || is_primlong te) && eq_type t te
                                                        then OK (te, ef)
                                                        else Error (msg "TYPE ERROR: Wrong argument type to unary minus operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Unary operator")
                                          end
                            | Cop.Oabsfloat => Error (msg "TYPE ERROR: Floating-point absolute value operator is not supported in BeePL")
                            end 
                 | Bop o => match o with 
                            | Cop.Oadd => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(te1, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to add operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end 
                            | Cop.Osub => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                               then OK(te1, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to add operator, it expects int or long as argument") 
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Omul => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to mul operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end 
                            | Cop.Odiv => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to div operator, it expects int or long as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Omod => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to mod operator, it expects int or long as argument") 
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oand => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to and operator, it expects bool as argument")
                                          | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oor => match es with 
                                         | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to or operator, it expects bool as argument")
                                         | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                         end
                            | Cop.Oxor => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to xor operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oshl => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to shl operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oshr => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                           do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                           if (eq_type te1 te2 && (is_primint32 te1 || is_primlong te1) && eq_type te1 t) 
                                                           then OK(te1, ef1 ++ ef2)
                                                           else Error (msg "TYPE ERROR: Wrong argument types to shr operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oeq => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1 || is_primbool te2) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to eq operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.One => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1 || is_primbool te2) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ne operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Olt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to lt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ogt => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to gt operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Ole => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to le operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            | Cop.Oge => match es with 
                                          | e1 :: e2 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                               do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                                                               if (eq_type te1 te2 && (is_primint te1 || is_primlong te1) && eq_type (Vtype Tbool) t)
                                                               then OK(Vtype Tbool, ef1 ++ ef2)
                                                               else Error (msg "TYPE ERROR: Wrong argument types to ge operator, it expects int or long as argument")
                                          | _ =>  Error (msg "TYPE ERROR: Wrong number of arguments to Binary operators") 
                                          end
                            end
                 | ArrayRead n => match es with
                     | e :: nil => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                         match te with
                         | Atype elem len a =>
                             if Nat.ltb n (Z.to_nat len) && eq_type elem t && negb (is_funtype elem)
                             then OK (elem, ef)
                             else Error (msg "TYPE ERROR: Invalid array read index or result type")
                         | _ => Error (msg "TYPE ERROR: Array read expects an array")
                         end
                     | _ => Error (msg "TYPE ERROR: Array read expects one argument")
                     end
                 | Cast target => match target with
                             | Vtype vt => match es with 
                                           | e1 :: nil => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                                                          match te1 with 
                                                          | Vtype vt1 => do rt <- allowed_cast vt1 vt;
                                                                         if eq_type t (Vtype vt)
                                                                         then OK(Vtype rt, ef1)
                                                                         else Error (msg "TYPE ERROR: Cast result annotation must match its target")
                                                          | _ => Error (msg "TYPE ERROR: Wrong argument type to casting operator, it expects bool, int, or long")
                                                          end
                                           | _ => Error (msg "TYPE ERROR: Wrong number of arguments to Casting Operator")
                                           end 
                             | _ => Error (msg "TYPE ERROR: Casting is only allowed from one value type to another")
                             end
                 end
| Bind x t e1 e2 t' => do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv (extend_context Gamma x t) Sigma e2;
                       if eq_type te1 t && eq_type te2 t'
                       then OK (te2, ef1 ++ ef2)
                       else Error (msg "TYPE ERROR: Type of bind does not match the inferred type")
| Cond e1 e2 e3 t =>  do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                      do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                      do (te3, ef3) <- type_check_expr cenv Gamma Sigma e3;
                      if is_primbool te1 && eq_type te2 te3 && eq_type t te2
                      then OK (te2, ef1 ++ ef2 ++ ef3)
                      else Error (msg "TYPE ERROR: Type of cond does not match the inferred type")
| Unit t => if eq_type t Utype then OK (Utype, nil)
            else Error (msg "TYPE ERROR: Unit expression requires unit annotation")
| Addr l ofs t =>  match PTree.get l.(lname) Sigma with 
                   | Some (Ptrtype (Reftype bt a)) => if eq_type t (Ptrtype (Reftype bt a))
                                              then OK (Ptrtype (Reftype bt a), nil)
                                              else Error (msg "Type of location does not match the inferred type")
                   | Some _ => Error (msg "TYPE ERROR: Wrong type inferred for location")
                   | None => Error (msg "TYPE ERROR: Location not found")
                   end
(*| Eapp ef ts es t => Error (msg "TYPE ERROR: We have no use case of builtin function as of now")*)
| Sinit x ids es t => do (tes, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
    match t with
    | Stype id a | Ptrtype (Reftype (Bstruct id a) _) =>
        if ident_eq x id then
          match cenv!id with
          | Some co =>
              if list_eq_dec ident_eq ids
                (map Ctypes.name_member
                  (bmembers_cmembers (filter (fun m => negb (member_is_padding m)) co.(co_members))))
              then do bts <- source_member_types ids co.(co_members);
                   if eq_types eq_type tes bts
                   then if storage_type_check cenv (Stype id a)
                        then OK (t, efs)
                        else Error (msg "TYPE ERROR: Struct storage contains an invalid memory slot or extent")
                   else Error (msg "TYPE ERROR: Struct initializer source field types do not match")
              else Error (msg "TYPE ERROR: Struct initializer must list every field in declaration order")
          | None => Error (msg "TYPE ERROR: Struct fields not found in composite env")
          end
        else Error (msg "TYPE ERROR: Struct initializer header does not match its result type")
    | _ => Error (msg "TYPE ERROR: Struct initializer requires a struct or struct reference type")
    end
| Sfield e x t => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                  match te with 
                  | Stype id a => match cenv!id with 
                                  | Some co => do bt <- type_of_bfield x co.(co_members);
                                               if eq_type t bt 
                                               then OK (bt, ef)
                                               else Error (msg "TYPE ERROR: Wrong type inferred for the struct field")
                                  | None => Error (msg "TYPE ERROR: The field accessed from the struct is not found in composite env")
                                  end
                  | Ptrtype (Reftype (Bstruct id a) _) => match cenv!id with 
                                             | Some co => do bt <- type_of_bfield x co.(co_members);
                                               if eq_type t bt 
                                               then OK (bt, ef)
                                               else Error (msg "TYPE ERROR: Wrong type inferred for the struct field")
                                             | None => Error (msg "TYPE ERROR: The field accessed from the struct is not found in composite env")
                                            end
                  | _ => Error (msg "TYPE ERROR: Should be a struct type")
                  end
| For e1 e2 d e t =>   do (te1, ef1) <- type_check_expr cenv Gamma Sigma e1;
                       do (te2, ef2) <- type_check_expr cenv Gamma Sigma e2;
                       do (te, ef) <- type_check_expr cenv Gamma Sigma e;
                       let fv1 := free_variables e1 in 
                       let fv2 := free_variables e2 in
                       let fv := free_variables e in 
                       if (eq_type te1 te2 
                           && eq_effect ef1 nil 
                           && eq_effect ef2 nil 
                           && ((is_primint te1) || (is_primlong te2))
                           && eq_type te t && eq_type t Utype && disjoint_vars fv fv1 && disjoint_vars fv fv2)
                       then OK(te, ef1 ++ ef2 ++ ef)
                       else Error (msg "TYPE ERROR: The range type should be unsigned int or long and the inferred type does not match")
                                                          
| Enone t => match t with
             | Ptrtype (Otype inner) => if negb (is_option_ptr_type inner)
                             then OK(t, nil)
                             else Error (msg "TYPE ERROR: Nested optional references have no nullable-pointer representation")
             | _ => Error (msg "TYPE ERROR: Type of Enone should be an option to ref type")
             end
| Esome e t => do (te, ef) <- type_check_expr cenv Gamma Sigma e;
               match t with 
               | Ptrtype (Otype t') => if negb (is_option_ptr_type t') && eq_type te (Ptrtype t')
                               then OK(t, ef)
                               else Error (msg "TYPE ERROR: Type of Esome should be an option to ref type")
               | _ => Error (msg "TYPE ERROR: Type of Esome should be an option type")
               end
| Match e ps es t =>
    do (te, ef) <- type_check_expr cenv Gamma Sigma e;
    match te with
    | Ptrtype (Otype inner) =>
        if is_option_ptr_type inner then
          Error (msg "TYPE ERROR: Nested optional references have no nullable-pointer representation")
        else
          match ps, es with
          | Pnone :: Psome x :: nil, enone :: esome :: nil =>
              do (tn, efn) <- type_check_expr cenv Gamma Sigma enone;
              do (ts, efs) <- type_check_expr cenv (extend_context Gamma x (Ptrtype inner)) Sigma esome;
              if eq_type tn t && eq_type ts t then OK (t, ef ++ efn ++ efs)
              else Error (msg "TYPE ERROR: Option branches must match the result type")
          | Psome x :: Pnone :: nil, esome :: enone :: nil =>
              do (ts, efs) <- type_check_expr cenv (extend_context Gamma x (Ptrtype inner)) Sigma esome;
              do (tn, efn) <- type_check_expr cenv Gamma Sigma enone;
              if eq_type ts t && eq_type tn t then OK (t, ef ++ efs ++ efn)
              else Error (msg "TYPE ERROR: Option branches must match the result type")
          | _, _ => Error (msg "TYPE ERROR: Option match requires exactly none and some branches")
          end
    | Bytes =>
        match ps, es with
        | Pbytes header (Stype sid attr) fields :: Pbytes rest Bytes nil :: nil,
          yes :: no :: nil =>
            if packet_schema_check cenv sid fields then
            if attr_eq attr noattr then
            do (tyes, efyes) <- type_check_expr cenv
              (extends_context (extend_context Gamma header (Stype sid attr))
                (unzip1 fields) (unzip2 fields)) Sigma yes;
            do (tno, efno) <- type_check_expr cenv (extend_context Gamma rest Bytes) Sigma no;
            if eq_type tyes t && eq_type tno t then OK (t, ef ++ efyes ++ efno)
            else Error (msg "TYPE ERROR: Packet branches must match the result type")
            else Error (msg "TYPE ERROR: Packet header pattern must use default attributes")
            else Error (msg "TYPE ERROR: Packet schema or field bindings are invalid")
        | _, _ => Error (msg "TYPE ERROR: Packet match requires a struct pattern and bytes fallback")
        end
    | _ => Error (msg "TYPE ERROR: Match expects an option or bytes type")
    end
| Ebytes es t => Error (msg "TYPE ERROR: Type checking of Bitstrings are not supported yet")
| Ainit a t es t' => do (ts, efs) <- type_check_exprs type_check_expr cenv Gamma Sigma es;
    match t with
    | Atype elem len attr =>
        if eq_type t t' && Z.eqb len (Z.of_nat (List.length ts)) && all_eq_type elem ts
        then if storage_type_check cenv t
             then OK (t', efs)
             else Error (msg "TYPE ERROR: Array storage type is incomplete, volatile, unrepresentable, or contains functions")
        else Error (msg "TYPE ERROR: Array annotations, length, or element types disagree")
    | _ => Error (msg "TYPE ERROR: Array initialization expects an array annotation")
    end
| CallFrame _ _ _ | LoopFrame _ _ _ => Error (msg "TYPE ERROR: Internal runtime frames are not source expressions")
| Aaccess a t n t' =>
    match Gamma ! a with
    | None => Error (msg "TYPE ERROR: Unbound array name")
    | Some declared =>
        match t with
        | Atype elem len attr =>
            if eq_type declared t && eq_type elem t' && Nat.ltb n (Z.to_nat len) && negb (is_funtype elem)
            then OK (t', nil)
            else Error (msg "TYPE ERROR: Array binding, element type, or index mismatch")
        | _ => Error (msg "TYPE ERROR: Array access expects an array")
        end
    end

end.

Open Scope string_scope.

Definition type_check_function (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : function) : res string :=
let Gamma' := bind_vars Gamma fn.(fn_args) in
if parameters_storage_check cenv fn.(fn_args) then
if list_norepet_dec ident_eq (unzip1 fn.(fn_args)) then
match type_check_expr cenv Gamma' Sigma fn.(fn_body) with 
| Error msg => Error msg
| OK tef =>  if eq_type fn.(fn_return) tef.1 && eq_effect fn.(fn_effect) tef.2 
             then if is_ptrtype tef.1 == false 
                  then OK "SUCCESS: Function type checks!" 
                  else Error (msg "TYPE ERROR: Function declaration cannot return an address")
             else Error (msg "TYPE ERROR: Type from function body does not match with the return type in the function declaration")
end
else Error (msg "TYPE ERROR: Function parameter names must be distinct")
else Error (msg "TYPE ERROR: Function data parameters require complete, nonvolatile storage types").

Definition type_check_fundef (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (fn : BeePL.fundef) : res string :=
match fn with 
| Internal f => type_check_function cenv Gamma Sigma f 
| External ef ts t cc => match ef with 
                         | EF_external fn fs => do efs <- get_ef_type efenv (get_name_eapp ef);
                                                if eq_type t (get_rt_eapp ef) 
                                                then if eq_types eq_type ts (get_at_eapp ef)
                                                     then if eq_types eq_type ts (fst efs) 
                                                          then if eq_type t (fst (snd efs))
                                                               then if eq_effect (get_ef_eapp ef) (snd (snd efs)) 
                                                                    then OK "SUCCESS: Fundef type checks!" 
                                                                    else Error (msg "TYPE ERROR: Effect of external function is not as expected")
                                                               else Error (msg "TYPE ERROR: Return type of external function is not as expected")
                                                          else Error (msg "TYPE ERROR: Argument types of external function is not as expected")
                                                      else Error (msg "TYPE ERROR: Argument types of external function is not as given in signature")
                                                else Error (msg "TYPE ERROR: Return type of external function is not as given in signature")
                                                
                         end
end.

Definition type_check_globvar (efenv : ef_env) (Gamma : ty_context) (Sigma : store_context) (gv : BeePL.globvar type) : res (type * effect) :=
do ef <- construct_ef_gvars gv.(gvar_init);
OK (gv.(gvar_info), ef).


Section Type_check_globdefs.

Variable type_check_globdef : ef_env -> bcomposite_env -> ty_context -> store_context -> BeePL.globdef BeePL.fundef BeeTypes.type -> res string.

Fixpoint type_check_globdefs (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context) (gds : list (BeePL.globdef BeePL.fundef BeeTypes.type)) : res string :=
match gds with 
| nil => OK "SUCCESS: Program type checks!"
| gd :: gds => do gds1 <- type_check_globdef efenv cenv Gamma Sigma gd;
               type_check_globdefs efenv cenv Gamma Sigma gds
end.
  
End Type_check_globdefs.

Definition type_check_globdef (efenv : ef_env) (cenv : bcomposite_env) (Gamma : ty_context) (Sigma : store_context)  (gd : BeePL.globdef BeePL.fundef BeeTypes.type) : res string :=
match gd with 
| AST.Gfun f => type_check_fundef efenv cenv Gamma Sigma f  
| Gvar g => do gt <- type_check_globvar efenv Gamma Sigma g;
            OK "SUCCESS: Program type checks!"
end.

(* Store context: Not needed in the executable type checker because location is never used by programmer, it only comes as intermediate results in semantics *) 
Definition type_check_program (p : BeePL.program) : res string :=
let sb := check_get_fundef_sec p.(prog_defs) in 
let defs := map (fun '(id, gd, _) => (id, gd)) p.(prog_defs) in
let Gamma := bind_globdef (PTree.empty _) defs in
let cenv := p.(prog_comp_env) in 
if sb then
type_check_globdefs type_check_globdef beepl_ef_env cenv Gamma empty_context (unzip2 defs)
else Error (msg "TYPE ERROR: Section attribute related to program type").
