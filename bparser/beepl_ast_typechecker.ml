open Beepl_ast

exception TypeError of string

module Env = Map.Make(String)
type tyenv = typ Env.t

module Senv = struct
  module M = Map.Make(String)
  type t = (string * typ) list M.t

  let empty = M.empty
  let add (sname : string) (fields : (string * typ) list) (m : t) = M.add sname fields m

  let find (sname : string) (m : t) =
    try M.find sname m with Not_found ->
      raise (TypeError (Printf.sprintf "Unknown struct %s" sname))

  (* Turn a source name like "xdp_md" or "_data" into the Coq variable
   that holds its ident: e.g., "_xdp_md" or "__data". *)

  let find_field (sname : string) (fname : string) (m : t) =
    let fields = find sname m in
    match List.assoc_opt fname fields with
    | Some ty -> ty
    | None ->
        raise (TypeError (Printf.sprintf "Unknown field %s of struct %s" fname sname))

  let fields_of sname m = find sname m
end

(* Build a struct environment from StructDecls *)
let build_senv (prog : Beepl_ast.program) : Senv.t =
  List.fold_left
    (fun acc -> function
      | Beepl_ast.StructDecl (name, fields, _sec) ->
          Senv.add name fields acc
      | _ -> acc)
    Senv.empty
    prog

type efinfo = {
  formals  : typ list;     (* fixed prefix *)
  effects  : effect list;
  ret      : typ;
  variadic : bool;
}
    
type efenv = efinfo Env.t
    
let build_efenv () : efenv =
  Env.empty
  |> Env.add "printf"
        { formals = [ Ptr (Reftype (Bprim Tint8)) ];
          effects = [Io];
          ret = Vtype Tint32;
          variadic = true }
  |> Env.add "scanf"
  { formals = [ Ptr (Reftype (Bprim Tint8)) ];
    effects = [Io];
    ret = Vtype Tint32;
    variadic = true }
  |> Env.add "bpf_printk"
  { formals = [ Ptr (Reftype (Bprim Tint8)); Vtype Tint32];
    effects = [Io];
    ret = Vtype Tint32;
    variadic = true }
  |> Env.add "bpf_get_prandom_u32"
        { formals = [];
          effects = [Io];
          ret = Vtype Tuint32;
          variadic = false }
  |> Env.add "bpf_ktime_get_ns"
        { formals = [];
          effects = [Io];
          ret = (* prefer Tuint64 if you have it *) Vtype Tulong;
          variadic = false }
  |> Env.add "bpf_skb_change_type"
        { formals = [Ptr (Reftype (Bstruct "__sk_buff")); Vtype Tuint32];
          effects = [Write; Io];
          ret = Vtype Tlong;
          variadic = false }
  |> Env.add "bpf_skb_load_bytes"
        { formals = [Ptr (Reftype (Bstruct "__sk_buff")); Vtype Tuint32;
                     Ptr (Reftype (Bprim Tuint32)); Vtype Tuint32];
          effects = [Read; Write; Io]; ret = Vtype Tlong; variadic = false }
  |> Env.add "bpf_skb_store_bytes"
        { formals = [Ptr (Reftype (Bstruct "__sk_buff")); Vtype Tuint32;
                     Ptr (Reftype (Bprim Tuint32)); Vtype Tuint32; Vtype Tulong];
          effects = [Read; Write; Io]; ret = Vtype Tlong; variadic = false }
  |> Env.add "bpf_redirect"
        { formals = [Vtype Tuint32; Vtype Tulong];
          effects = [Io]; ret = Vtype Tlong; variadic = false }
  |> Env.add "bpf_get_current_pid_tgid"
        { formals = [];
          effects = [Io];
          ret = Vtype Tulong;
          variadic = false }
  |> Env.add "htons"
        { formals = [ Vtype Tuint16 ];
          effects = [];
          ret = Vtype Tuint16;
          variadic = false }
    |> Env.add "bpf_get_current_comm"
     { formals = [ Ptr (Reftype (Bprim Tint8)); Vtype Tuint32 ];
       effects = [Io];
       ret = Vtype Tlong;       (* Linux returns long; Tulong also ok if you prefer *)
       variadic = false }

  |> Env.add "bpf_probe_read_user_str"
     { formals = [ Ptr (Reftype (Bprim Tint8)); Vtype Tuint32; Ptr (Reftype (Bprim Tint8)) ];
       effects = [Io];
       ret = Vtype Tlong;
       variadic = false }

  |> Env.add "bpf_map_lookup_elem"
     { formals = [Beepl_maps.handle_type; Ptr (Reftype (Bprim Tuint32))];
       effects = [Read; Io]; ret = Ptr (Otype (Reftype (Bprim Tulong))); variadic = false }
  |> Env.add "bpf_map_update_elem"
     { formals = [Beepl_maps.handle_type; Ptr (Reftype (Bprim Tuint32));
                  Ptr (Reftype (Bprim Tulong)); Vtype Tulong];
       effects = [Write; Io]; ret = Vtype Tlong; variadic = false }
  |> Env.add "bpf_map_delete_elem"
     { formals = [Beepl_maps.handle_type; Ptr (Reftype (Bprim Tuint32))];
       effects = [Write; Io]; ret = Vtype Tlong; variadic = false }

let extern_bindings_of_efenv (ee : efenv) : (string * typ) list =
  Env.bindings ee
  |> List.map (fun (name, info) ->
        (name, Ftype (info.formals, info.effects, info.ret, info.variadic)))

let rec take n xs =
  match n, xs with
  | 0, _ | _, [] -> []
  | n, x :: xs -> x :: take (n - 1) xs

let rec drop n xs =
  match n, xs with
  | 0, _ -> xs
  | _, [] -> []
  | n, _::tl -> drop (n-1) tl

let string_of_ptype = function
  | Tbool -> "bool"
  | Tint8 -> "int8"
  | Tuint8 -> "uint8"
  | Tint16 -> "int16"
  | Tuint16 -> "uint16"
  | Tint32 -> "int32"
  | Tuint32 -> "uint32"
  | Tlong -> "long"
  | Tulong -> "ulong"

let rec string_of_ptr_typ = function 
  | Reftype (btype) -> 
    let bstr = match btype with
      | Bprim pt -> string_of_ptype pt
      | Bstruct s -> "struct " ^ s
      | Barray (pt, n) -> Printf.sprintf "array[%d] of %s" n (string_of_ptype pt)
    in
    Printf.sprintf "ref(%s)" bstr
  | Otype pt -> "opaque(" ^ string_of_ptr_typ pt ^ ")"

let rec string_of_typ = function
  | Utype -> "unit"
  | Vtype pt -> string_of_ptype pt
  | Ptr pt -> "ptr to " ^ (string_of_ptr_typ pt)
  | Stype s -> "struct " ^ s
  | Atype (t, n) -> Printf.sprintf "array[%d] of %s" n (string_of_typ t)
  | Ftype _ -> "function type"
  | Bytes -> "bytes"

let list_to_env (xs : (string * typ) list) : tyenv =
  List.fold_left (fun acc (x, ty) -> Env.add x ty acc) Env.empty xs
let ptype_eq p1 p2 =
  match p1, p2 with
  | Tbool, Tbool -> true
  | Tuint8, Tuint8 -> true
  | Tint8, Tint8 -> true
  | Tuint16, Tuint16 -> true
  | Tint16, Tint16 -> true
  | Tuint32, Tuint32 -> true
  | Tint32, Tint32 -> true
  | Tulong, Tulong -> true
  | Tlong, Tlong -> true
  | _ -> false

let rec typ_eq t1 t2 =
  match t1, t2 with
  | Utype, Utype -> true
  | Vtype p1, Vtype p2 -> ptype_eq p1 p2
  | Ftype (args1, effs1, ret1, v1), Ftype (args2, effs2, ret2, v2) ->
    List.length args1 = List.length args2 &&
    List.for_all2 typ_eq args1 args2 &&
    effs1 = effs2 &&
    typ_eq ret1 ret2 &&
    v1 = v2
  | Ptr (Reftype (b1)), Ptr (Reftype (b2)) ->
    (match b1, b2 with
    | Bprim p1, Bprim p2 -> ptype_eq p1 p2
    | Bstruct s1, Bstruct s2 -> s1 = s2
    | Barray (pt1, n1), Barray (pt2, n2) ->
        n1 = n2 && ptype_eq pt1 pt2
    | _ -> false)
  | Stype s1, Stype s2 -> s1 = s2
  | Atype (elem1, n1), Atype (elem2, n2) -> n1 = n2 && typ_eq elem1 elem2
  | Ptr (Otype pt1), Ptr (Otype pt2) -> typ_eq (Ptr pt1) (Ptr pt2)
  | Bytes, Bytes -> true
  | _, _ -> false

let rec infer_expr (ee : efenv) (senv : Senv.t) (env : tyenv) (e : expr) : typ =
  match e with
  | Var x ->
      (match Env.find_opt x env with
       | Some ty -> ty
       | None -> raise (TypeError ("Unbound variable: " ^ x)))
  | Const c -> 
      (match c with
       | Cunit -> Utype
       | Cbool _ -> Vtype Tbool
       | Cint32 _ -> Vtype Tint32
       | Clong _ -> Vtype Tlong
       | Cstring s -> Ptr (Reftype (Bprim (Tint8)))) (* Assuming string is a byte array and max length *)
  | Prim (Uop uop, args) ->
    (match args with 
    | [arg] -> let arg_ty = infer_expr ee senv env arg in
        begin match uop with
        | Oneg ->
            begin match arg_ty with
            | Vtype Tint32 | Vtype Tlong | Vtype Tulong -> arg_ty
            | _ -> raise (TypeError "- can only be applied to int32 or long")
            end
        | Onotint ->
            begin match arg_ty with
            | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
            | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32 -> arg_ty
            | _ -> raise (TypeError "~ can only be applied to integer types")
            end
        | Onotbool ->
            if arg_ty = Vtype Tbool then Vtype Tbool
            else raise (TypeError "~ can only be applied to bool")
        | UOverloadTilde ->
            begin match arg_ty with
            | Vtype Tbool -> Vtype Tbool
            | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
            | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32 -> arg_ty
            | _ -> raise (TypeError "Overloaded `~` can only be applied to bool or integer types")
            end
          end
      |  _ ->
        raise (TypeError "Unary operator expects exactly one argument"))
  | Prim (Bop bop, args) ->
    begin match args with 
      | [a1; a2] ->
        let t1 = infer_expr ee senv env a1 in
        let t2 = infer_expr ee senv env a2 in
        begin match bop with
        | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor | Oshl | Oshr  ->
            if (typ_eq t1 t2) && (match t1 with
              | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
              | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32
              | Vtype Tlong | Vtype Tulong -> true
              | _ -> false)
            then t1
            else raise (TypeError "+, -, *, /, mod, and, or, xor, <<, >> can only be applied to matching integer/long types")
        | Oeq | One ->
              if (typ_eq t1 t2) && (match t1 with
                | Vtype Tbool | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
                | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32
                | Vtype Tlong | Vtype Tulong -> true
                | _ -> false)
              then Vtype Tbool
              else raise (TypeError "==, != can only be applied to matching integer/long/bool types")
        | Olt | Ogt | Ole | Oge ->
              if (typ_eq t1 t2) && (match t1 with
                | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
                | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32
                | Vtype Tlong | Vtype Tulong -> true
                | _ -> false)
                then Vtype Tbool
                else raise (TypeError "<,>,<=,>= can only be applied to matching integer/long types")
        (* Add other binary operators here as needed *)
        end
      | _ -> raise (TypeError "Binary operator expects exactly two arguments")
      end
  | Prim (Cast t, args) ->
    begin match args with
    | [arg] ->
        let arg_ty = infer_expr ee senv env arg in
        begin match arg_ty, t with
        | Vtype ta, Vtype _ -> t
        | _ -> raise (TypeError "Cast can only be applied between primitive types")
        end
    | _ -> raise (TypeError "Cast expects exactly one argument")
    end
  | Prim (Ref, args) ->
    begin match args with
    | [arg] ->
        let arg_ty = infer_expr ee senv env arg in
        Ptr (Reftype (match arg_ty with
          | Vtype pt -> Bprim pt
          | Stype s -> Bstruct s
          | Atype (Vtype pt, n) -> Barray (pt, n)  (* Array type with known size *)
          | _ -> raise (TypeError "Can only take reference of basic types")))
    | _ -> raise (TypeError "Ref expects exactly one argument")
    end 
  | Prim (Deref, args) ->
    begin match args with
    | [arg] ->
        let arg_ty = infer_expr ee senv env arg in
        begin match arg_ty with
        | Ptr (Reftype (Bstruct "bpf_sock_create")) ->
            raise (TypeError "Socket-create context only supports scalar field reads")
        | Ptr (Reftype (Bstruct "bpf_raw_sys_enter")) ->
            raise (TypeError "Raw tracepoint context only exposes syscall_id")
        | Ptr (Reftype (btype)) ->
            begin match btype with
            | Bprim pt -> Vtype pt
            | Bstruct s -> Stype s
            | Barray (pt, n) -> Atype (Vtype pt, n)  (* Array type with known size *)
            end
        | Ptr (Otype _) ->
            raise (TypeError "Deref cannot be applied to option type, it should be wrapped inside match")
        | _ -> raise (TypeError "Deref can only be applied to pointer types")
        end
    | _ -> raise (TypeError "Deref expects exactly one argument")
    end
  | Prim (Massgn, args) ->
    begin match args with
    | [arg1; arg2] ->
        let t1 = infer_expr ee senv env arg1 in
        let t2 = infer_expr ee senv env arg2 in
        begin match t1 with
        | Ptr (Reftype (Bstruct "bpf_sock_create")) ->
            raise (TypeError "Socket-create context is read-only")
        | Ptr (Reftype (Bstruct "bpf_raw_sys_enter")) ->
            raise (TypeError "Raw tracepoint context is read-only")
        | Ptr (Reftype (btype)) ->
            let expected_ty = match btype with
              | Bprim pt -> Vtype pt
              | Bstruct s -> Stype s
              | Barray (pt, n) -> Atype (Vtype pt, n)  (* Array type with known size *)
            in
            if typ_eq expected_ty t2 then Utype
            else raise (TypeError "Massgn type mismatch")
        | Ptr (Otype _) ->
            raise (TypeError "Massgn cannot be applied to option type, it should be wrapped inside match")
        | _ -> raise (TypeError "Massgn can only be applied to pointer types")
        end
    | _ -> raise (TypeError "Massgn expects exactly two arguments")
    end
  | App (e1, args) ->
    let literal n = function
      | Prim (Cast _, [Const (Cint32 x)]) -> x = Int32.of_int n
      | _ -> false in
    (match e1, args with
     | Var ("bpf_skb_load_bytes" | "bpf_skb_store_bytes"), _ :: _ :: _ :: len :: _ ->
         if not (literal 4 len) then
           raise (TypeError "Packet helper length must be literal (uint32)4 for a uint32 buffer")
     | _ -> ());
    (match e1, args with
     | Var "bpf_skb_store_bytes", [_; _; _; _; flags]
     | Var "bpf_redirect", [_; flags] ->
         if not (literal 0 flags) then
           raise (TypeError "Packet helper flags must be literal (ulong)0")
     | _ -> ());
    let ty1      = infer_expr ee senv env e1 in
    let arg_tys  = List.map (infer_expr ee senv env) args in
    begin match ty1 with
    | Ftype (formals, _eff, ret_type, va) ->
        let n_formals = List.length formals in
        let n_actuals = List.length arg_tys in
        if n_actuals < n_formals || (not va && n_actuals <> n_formals) then
          raise (TypeError (Printf.sprintf
            "Function application expects %s%d arguments, got %d"
            (if va then "at least " else "") n_formals n_actuals));
        (*and n_actuals = List.length arg_tys in*)

        (* Does the callee name correspond to a known external variadic? *)
        let callee_is_variadic =
          match e1 with
          | Var fname ->
              (match Env.find_opt fname ee with
                | Some info -> info.variadic
                | None -> false)
          | _ -> false
        in

        if callee_is_variadic then (
          let tail = drop n_formals arg_tys in
          let max_payload = 3 in  (* fmt,len + up to 3 payloads -> 5 arg regs *)
          if List.length tail > max_payload then
            raise (TypeError "bpf_printk: at most 3 variadic payload args are allowed");
      
          (* allow integers/longs AND pointers as payloads; exporter will cast to u64 *)
          let is_intlike = function
            | Vtype Tint8 | Vtype Tuint8
            | Vtype Tint16 | Vtype Tuint16
            | Vtype Tint32 | Vtype Tuint32
            | Vtype Tlong  | Vtype Tulong -> true
            | _ -> false
          in
          List.iter (fun ty ->
            match ty with
            | Ptr _ -> ()           (* pointers are allowed *)
            | _ when is_intlike ty -> ()
            | _ -> raise (TypeError "Variadic args must be integers/longs or pointers"))
            tail
        );
      

        (* Always check the fixed prefix pairwise *)
        let prefix_actuals = take n_formals arg_tys in
        let ptype_eq p1 p2 =
          match p1, p2 with
          | Tbool, Tbool -> true
          | Tuint8, Tuint8 | Tint8, Tint8
          | Tuint16, Tuint16 | Tint16, Tint16
          | Tuint32, Tuint32 | Tint32, Tint32
          | Tulong, Tulong | Tlong, Tlong -> true
          | _ -> false
        in
        
        let arg_compatible (formal : typ) (actual : typ) : bool =
          (* exact match is always ok *)
          typ_eq formal actual ||
          (* array-to-pointer decay: Vtype pt [n] can be used where Ptr(Reftype(_, Bprim pt)) is expected *)
          match formal, actual with
          | Ptr (Reftype (Bprim ptf)), Atype (Vtype pta, _n) when ptype_eq ptf pta -> true
          | _ -> false
        in
        
        List.iter2 (fun formal actual ->
          if not (arg_compatible formal actual) then
            raise (TypeError (Printf.sprintf
              "Function application argument type mismatch: expected %s, got %s"
              (string_of_typ formal) (string_of_typ actual)))          
        ) formals prefix_actuals;
        ret_type

    | _ ->
        raise (TypeError "Expected a function type in application")
    end
  | Let (x, ty, e1, e2) ->
      (* disallow duplicate names *)
      if Env.mem x env then
        raise (TypeError (Printf.sprintf "Duplicate variable: %s" x));
  
      let t1 = infer_expr ee senv env e1 in
      if not (typ_eq t1 ty) then
        raise (TypeError "Type mismatch in let-binding");
  
      let env' = Env.add x ty env in
      infer_expr ee senv env' e2
  | If (e1, e2, e3) ->
      let t1 = infer_expr ee senv env e1 in
      if not (typ_eq t1 (Vtype Tbool)) then
        raise (TypeError "If condition must be bool");
      let t2 = infer_expr ee senv env e2 in
      let t3 = infer_expr ee senv env e3 in
      if not (typ_eq t2 t3) then
        raise (TypeError "If branches have mismatched types");
      t2
  | For (e1, e2, d, e3) ->
      let t1 = infer_expr ee senv env e1 in
      let t2 = infer_expr ee senv env e2 in
      let t3 = infer_expr ee senv env e3 in
      if (typ_eq t1 t2) && (match t1 with
        | Vtype Tint8 | Vtype Tint16 | Vtype Tint32
        | Vtype Tuint8 | Vtype Tuint16 | Vtype Tuint32
        | Vtype Tlong | Vtype Tulong -> true
        | _ -> false)
      then
        if typ_eq t3 Utype then Utype
        else raise (TypeError "For loop body must have unit type")
      else raise (TypeError "For loop bounds must be matching integer/long types")
  | Sinit (struct_name, fields, exprs) ->
        let decl = Senv.find struct_name senv in
        let decl_names, _ = List.split decl in
    
        (* 1) arity + exact ordered field list *)
        if List.length fields <> List.length exprs
           || fields <> decl_names
        then
          raise (TypeError "Struct initialization field list mismatch");
    
        (* 2) type-check values against declared types *)
        List.iter2 (fun fname expr ->
          let expected_ty = Senv.find_field struct_name fname senv in
          let expr_ty = infer_expr ee senv env expr in
          if not (typ_eq expected_ty expr_ty) then
            raise (TypeError (Printf.sprintf
              "Struct %s field %s type mismatch (expected %s, got %s)"
              struct_name fname (string_of_typ expected_ty) (string_of_typ expr_ty)))
        ) fields exprs;
    
        Stype struct_name
  | Fget (e, field_name) ->
      let e_ty = infer_expr ee senv env e in
      begin match e_ty with
      | Stype "bpf_raw_sys_enter"
      | Ptr (Reftype (Bstruct "bpf_raw_sys_enter")) when field_name <> "syscall_id" ->
          raise (TypeError "Raw tracepoint context only exposes syscall_id")
      | Stype struct_name ->
          let field_ty = Senv.find_field struct_name field_name senv in
          field_ty
      | Ptr (Reftype (Bstruct struct_name)) ->
          let field_ty = Senv.find_field struct_name field_name senv in
          field_ty
      | Ptr (Otype _) ->
          raise (TypeError "Field access through an optional pointer requires a some/none match")
      | _ -> raise (TypeError "Fget can only be applied to struct or pointer to struct types")
      end
  | Beepl_ast.Ainit (arr, exprs) ->
    (match exprs with
    | [] -> raise (TypeError "Ainit requires at least one element to infer type")
    | first_elem :: _ ->
        let elem_ty = infer_expr ee senv env first_elem in
        List.iter (fun expr ->
          let expr_ty = infer_expr ee senv env expr in
          if not (typ_eq elem_ty expr_ty) then
            raise (TypeError "Array initialization element type mismatch")
        ) exprs;
        Atype (elem_ty, List.length exprs))
  | Aaccess (arr, idx) ->
    (match Env.find_opt arr env with
    | Some (Atype (elem_ty, size)) ->
        if idx < 0 || idx >= size then
          raise (TypeError "Array access index out of bounds");
        elem_ty
    | Some _ -> raise (TypeError "Aaccess can only be applied to array types")
    | None -> raise (TypeError ("Unbound array variable: " ^ arr)))
  | Match (e, patterns, exprs) ->
      (* 1) scrutinee type *)
      let scrut_ty = infer_expr ee senv env e in
  
      (* arity check *)
      if List.length patterns <> List.length exprs then
        raise (TypeError "Match branches count mismatch");
  
      (* classify patterns *)
      let has_pbytes =
        List.exists (function Pbytes _ -> true | _ -> false) patterns in
      let has_opt =
        List.exists (function Psome _ | Pnone -> true | _ -> false) patterns in
  
      if has_pbytes && has_opt then
        raise (TypeError "Match: cannot mix Pbytes with option patterns (Psome/Pnone)");
      if has_pbytes then begin
        match patterns with
        | [Pbytes (_, Stype _, _); Pbytes (_, Bytes, [])] -> ()
        | _ -> raise (TypeError "Bytes match requires one struct pattern followed by a bytes fallback")
      end;
      if has_opt then begin
        let count pred = List.length (List.filter pred patterns) in
        if count (function Psome _ -> true | _ -> false) <> 1
           || count (function Pnone -> true | _ -> false) <> 1 then
          raise (TypeError "Option match requires exactly one some and one none branch")
      end;
  
      (* branch inference under the right discipline *)
      let infer_branch pat body =
        match pat with
        (* ---------- OPTION MODE ---------- *)
        | Pnone | Psome _ ->
            (* require option pointer scrutinee *)
            let inner_pt =
              match scrut_ty with
              | Ptr (Otype pt) -> pt
              | _ ->
                  raise (TypeError "Match on option requires scrutinee of type Ptr (Otype _)") in
            let env' =
              match pat with
              | Pnone   -> env
              | Psome x -> Env.add x (Ptr inner_pt) env
              | _       -> env (* unreachable here *)
            in
            infer_expr ee senv env' body
  
        (* ---------- BYTES MODE ---------- *)
        | Pbytes (s, t, fields) ->
            (* require bytes scrutinee *)
            (match scrut_ty with
             | Bytes -> ()
             | _ -> raise (TypeError "Pbytes requires scrutinee of type bytes"));
            (* (optional) sanity: the schema 't' for 's' should be a struct type *)
            (match t with
            | Stype name ->
                List.iter (fun (_, ty) -> match ty with
                  | Vtype _ -> ()
                  | _ -> raise (TypeError "Packet schemas currently require scalar fields; pointers cannot be deserialized"))
                  (Senv.fields_of name senv);
                List.iter (fun (field, ty) ->
                  let expected = Senv.find_field name field senv in
                  if not (typ_eq expected ty) then
                    raise (TypeError ("Pbytes field type mismatch: " ^ field))) fields
             | Bytes ->
                 if fields <> [] then
                   raise (TypeError "Bytes fallback cannot bind struct fields")
             | _ -> raise (TypeError "Pbytes schema must be a struct type (Stype ...)"));
            (* extend env with the packet-as-struct name and field bindings *)
            let env1 = Env.add s t env in
            let env' =
              List.fold_left
                (fun acc (fname, fty) -> Env.add fname fty acc)
                env1 fields
            in
            (* you may add extra checks here, e.g., that field types are byte-sized ints *)
            infer_expr ee senv env' body
      in
  
      let branch_tys =
        try List.map2 infer_branch patterns exprs with
        | Invalid_argument _ ->
            raise (TypeError "Match: internal arity error")
      in
  
      (* branches must agree on type *)
      (match branch_tys with
       | [] -> raise (TypeError "Match must have at least one branch")
       | ty0 :: rest ->
           if List.for_all (fun t -> typ_eq t ty0) rest then ty0
           else raise (TypeError "Match branches have mismatched types"))
  
  | Esome e_inner ->
    let te = infer_expr ee senv env e_inner in
    begin match te with 
              | Ptr pt  -> Ptr (Otype pt)
              | _ -> raise (TypeError "some expects a pointer type")
              end 
  | Enone ty ->
    begin match ty with
    | Ptr pt -> Ptr (Otype pt)
    | _ -> raise (TypeError "none expects a pointer type")
    end

    module StringSet = Set.Make(String)

    let check_unique (what : string) (name : string) (xs : (string * 'a) list) =
      let _, dups =
        List.fold_left
          (fun (seen, dups) (x, _) ->
             if StringSet.mem x seen then
               (seen, x :: dups)
             else
               (StringSet.add x seen, dups))
          (StringSet.empty, [])
          xs
      in
      match dups with
      | [] -> ()
      | dups ->
          let dups = List.rev dups in
          let msg =
            Printf.sprintf
              "Duplicate %s in function %s: %s"
              what name
              (String.concat ", " dups)
          in
          raise (TypeError msg)

    let infer_fundecl (ee : efenv)
    (Tfundecl (name, ret_type, eff, args, vars, body))
    (senv : Senv.t) (global_env : tyenv) =

  (* 0. Register this function's own type (non-vararg) for recursion *)
  let self_ty = Ftype (List.map snd args, eff, ret_type, false) in
  let global_env = Env.add name self_ty global_env in

  (* 1. Ensure all parameter names and local variable names are unique *)
  check_unique "parameters" name args;
  check_unique "locals"     name vars;
  check_unique "parameters/locals" name (args @ vars);

  (* 2. Build env with args + locals *)
  let env_with_args_and_vars =
    List.fold_left
      (fun acc (x, ty) -> Env.add x ty acc)
      global_env
      (args @ vars)
  in

  (* 3. Infer and check return type *)
  let inferred_type = infer_expr ee senv env_with_args_and_vars body in
  if not (typ_eq inferred_type ret_type) then
    raise (TypeError "Return type mismatch");
  (match ret_type with
   | Ptr _ -> raise (TypeError "Functions cannot return pointers to local storage")
   | _ -> ());
  ()

(* Kernel programs must have an acyclic, statically known call graph. *)
let check_ebpf_calls prog =
  let rec calls = function
    | App (Var name, args) -> name :: List.concat (List.map calls args)
    | App _ -> raise (TypeError "eBPF does not support indirect function calls")
    | Prim (_, es) | Sinit (_, _, es) | Ainit (_, es) ->
        List.concat (List.map calls es)
    | Let (_, _, a, b) -> calls a @ calls b
    | If (a, b, c) | For (a, b, _, c) -> calls a @ calls b @ calls c
    | Fget (e, _) | Esome e -> calls e
    | Match (e, _, es) -> calls e @ List.concat (List.map calls es)
    | Var _ | Const _ | Aaccess _ | Enone _ -> []
  in
  if List.exists (function EBPFInternal _ -> true | _ -> false) prog then begin
    let graph = List.filter_map (function
      | Internal (Tfundecl (name, _, _, _, _, body), _)
      | EBPFInternal (Tfundecl (name, _, _, _, _, body), _) ->
          Some (name, calls body)
      | _ -> None) prog in
    let rec visit path name =
      if List.mem name path then
        raise (TypeError ("Recursive eBPF call cycle involving " ^ name));
      match List.assoc_opt name graph with
      | None -> ()
      | Some children -> List.iter (visit (name :: path)) children
    in
    List.iter (fun (name, _) -> visit [] name) graph;
    let rec uses_tc_helper name =
      List.mem name ["bpf_skb_change_type"; "bpf_skb_load_bytes"; "bpf_skb_store_bytes"; "bpf_redirect"] ||
      match List.assoc_opt name graph with
      | None -> false
      | Some children -> List.exists uses_tc_helper children
    in
    let tc_section = function
      | None -> false
      | Some s ->
          let s = String.trim s in
          let s = if String.length s >= 8 && String.sub s 0 8 = "#section"
                  then String.trim (String.sub s 8 (String.length s - 8)) else s in
          s = "tc" || s = "\"tc\""
    in
    List.iter (function
      | EBPFInternal (Tfundecl (name, _, _, _, _, _), section)
        when not (tc_section section) && uses_tc_helper name ->
          raise (TypeError "bpf_skb_change_type currently requires a tc entry point; packet load/store/redirect helpers also require tc")
      | _ -> ()) prog
  end

let infer_program (prog : program) =
  List.iter (function
    | StructDecl ("bpf_sock_create", fields, _) ->
        if fields <> List.map (fun name -> (name, Vtype Tuint32))
          ["bound_dev_if"; "family"; "type"; "protocol"] then
          raise (TypeError "Socket-create context layout must be four uint32 fields: bound_dev_if, family, type, protocol")
    | StructDecl ("bpf_raw_sys_enter", fields, _) ->
        if fields <> [("reserved_regs", Vtype Tulong); ("syscall_id", Vtype Tlong)] then
          raise (TypeError "Raw tracepoint context layout must be reserved_regs:ulong, syscall_id:long")
    | _ -> ()) prog;
  (try Beepl_maps.prepare prog with Invalid_argument s -> raise (TypeError s));
  check_ebpf_calls prog;
  let senv = build_senv prog in  
  let ee    = build_efenv () in
  let extern_fun_types = extern_bindings_of_efenv ee in   
  (* Step 1: collect all top-level function types into global env *)
  let global_fun_types =
    List.filter_map (function
      | Internal (Tfundecl (name, ret, eff, args, _, _), _) ->
          Some (name, Ftype (List.map snd args, eff, ret, false))
      | EBPFInternal (Tfundecl (name, ret, eff, args, _, _), _) ->
          Some (name, Ftype (List.map snd args, eff, ret, false))
      | StructDecl (name, _, sec) when Beepl_maps.is_map_section sec -> Some (name, Beepl_maps.handle_type)
      | StructDecl _ -> None
      | GlobalLet (name, ty, _, _) -> Some (name, ty)
    ) prog
  in
  let global_env = list_to_env (extern_fun_types @ global_fun_types) in

  (* Step 2: typecheck each function body *)
  List.iter
    (function
      | Internal (f, _) | EBPFInternal (f, _) ->
          infer_fundecl ee f senv global_env
      | StructDecl _ -> ()
      | GlobalLet (name, ty, e, l) ->
          let inferred_ty = infer_expr ee senv global_env e in
          let string_array = match ty, e with
            | Atype (Vtype Tint8, n), Const (Cstring s) ->
                n = String.length s + 1
            | _ -> false in
          if not (string_array || typ_eq inferred_ty ty) then
            raise (TypeError ("Global let " ^ name ^ " type mismatch"))
        
    ) prog
