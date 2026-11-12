(* Surface nested options are elaborated into private ordinary structures.
   Run the surface checker before this pass, and check the resulting program
   again.  The core nullable-pointer ABI is unchanged at option depth one.
   Core soundness applies to the checked result; correctness of this surface
   elaboration is a separate simulation obligation. *)
open Beepl_ast
module TC = Beepl_ast_typechecker
module Names = Set.Make (String)

let lower_program (program : program) : program =
  let used = ref Names.empty in
  let reserve name = used := Names.add name !used in
  let rec reserve_type = function
    | Ptr pt -> reserve_pointer pt
    | Stype name -> reserve name
    | Atype (ty, _) -> reserve_type ty
    | Ftype (args, _, result, _) -> List.iter reserve_type args; reserve_type result
    | Utype | Vtype _ | Bytes -> ()
  and reserve_pointer = function
    | Reftype (Bstruct name) -> reserve name
    | Otype inner -> reserve_pointer inner
    | Reftype (Bprim _ | Barray _) -> () in
  let reserve_binding (name, ty) = reserve name; reserve_type ty in
  let reserve_pattern = function
    | Psome name -> reserve name
    | Pnone -> ()
    | Pbytes (name, ty, fields) ->
        reserve name; reserve_type ty; List.iter reserve_binding fields in
  let rec reserve_expr = function
    | Var name | Aaccess (name, _) -> reserve name
    | Const _ -> ()
    | App (callee, args) -> reserve_expr callee; List.iter reserve_expr args
    | Prim (op, args) ->
        (match op with Cast ty -> reserve_type ty | _ -> ()); List.iter reserve_expr args
    | Let (name, ty, first, body) -> reserve_binding (name, ty); reserve_expr first; reserve_expr body
    | If (a,b,c) | For (a,b,_,c) -> List.iter reserve_expr [a;b;c]
    | Sinit (name, fields, values) -> reserve name; List.iter reserve fields; List.iter reserve_expr values
    | Fget (value, field) -> reserve_expr value; reserve field
    | Ainit (name, values) -> reserve name; List.iter reserve_expr values
    | Match (value, patterns, branches) ->
        reserve_expr value; List.iter reserve_pattern patterns; List.iter reserve_expr branches
    | Esome value -> reserve_expr value
    | Enone ty -> reserve_type ty in
  List.iter (function
    | Internal (Tfundecl (name, result, _, args, locals, body), _)
    | EBPFInternal (Tfundecl (name, result, _, args, locals, body), _) ->
        reserve name; reserve_type result; List.iter reserve_binding (args @ locals); reserve_expr body
    | StructDecl (name, fields, _) -> reserve name; List.iter reserve_binding fields
    | GlobalLet (name, ty, value, _) -> reserve_binding (name,ty); reserve_expr value) program;
  let counter = ref 0 in
  let rec fresh role =
    let name = "__beepl_nested_option_" ^ role ^ "_" ^ string_of_int !counter in
    incr counter;
    if Names.mem name !used then fresh role else (reserve name; name) in
  let tag_type = Vtype (if Archi.ptr64 then Tulong else Tuint32) in
  let tag_value present =
    Prim (Cast tag_type,
      [if Archi.ptr64 then Const (Clong (if present then 1L else 0L))
       else Const (Cint32 (if present then 1l else 0l))]) in
  (* A structurally equal source option type has one private representation. *)
  let representations = Hashtbl.create 17 in
  let declarations = ref [] in
  let rec lower_type = function
    | Ptr (Otype (Otype _) as pt) -> let name,_,_ = representation pt in Stype name
    | Atype (ty, count) -> Atype (lower_type ty, count)
    | Ftype (args, effects, result, variadic) ->
        Ftype (List.map lower_type args, effects, lower_type result, variadic)
    | (Utype | Vtype _ | Ptr _ | Stype _ | Bytes) as ty -> ty
  and representation pt =
    match Hashtbl.find_opt representations pt with
    | Some desc -> desc
    | None ->
        let inner = match pt with
          | Otype (Otype _ as inner) -> inner
          | _ -> invalid_arg "Nested option representation requires at least two layers" in
        let payload_type = lower_type (Ptr inner) in
        let name = fresh "type" in
        let tag = fresh "tag" and payload = fresh "payload" in
        let desc = name,tag,payload in
        Hashtbl.add representations pt desc;
        (* Dependencies are emitted first when this reverse list is reversed. *)
        declarations := StructDecl (name, [(tag,tag_type);(payload,payload_type)], None) :: !declarations;
        desc in
  let rec absent = function
    | Otype (Otype _ as inner) as pt ->
        let name,tag,payload = representation pt in
        Sinit (name, [tag;payload], [tag_value false; absent inner])
    | Otype inner -> Enone (Ptr inner)
    | Reftype _ -> invalid_arg "Absent value requires an option type" in
  let ee = TC.build_efenv () in
  let senv = TC.build_senv program in
  let externals = TC.Env.fold (fun name (info : TC.efinfo) env ->
    TC.Env.add name (Ftype(info.TC.formals,info.TC.effects,info.TC.ret,info.TC.variadic)) env) ee TC.Env.empty in
  let globals = List.fold_left (fun env -> function
    | Internal (Tfundecl(name,result,effects,args,_,_),_)
    | EBPFInternal (Tfundecl(name,result,effects,args,_,_),_) ->
        TC.Env.add name (Ftype(List.map snd args,effects,result,false)) env
    | GlobalLet(name,ty,_,_) -> TC.Env.add name ty env
    | StructDecl(name,_,section) when Beepl_maps.is_map_section section ->
        TC.Env.add name Beepl_maps.handle_type env
    | StructDecl _ -> env) externals program in
  let add_bindings env bindings = List.fold_left (fun env (name,ty) -> TC.Env.add name ty env) env bindings in
  let infer env expr = TC.infer_expr ee senv env expr in
  let lower_pattern = function
    | Pbytes(name,ty,fields) -> Pbytes(name,lower_type ty,List.map(fun(name,ty)->name,lower_type ty)fields)
    | (Psome _ | Pnone) as pattern -> pattern in
  let branch_env env scrutinee_type = function
    | Psome name -> (match scrutinee_type with Ptr(Otype inner) -> TC.Env.add name (Ptr inner) env
        | _ -> raise (TC.TypeError "Option match requires an optional pointer"))
    | Pnone -> env
    | Pbytes(name,ty,fields) -> add_bindings (TC.Env.add name ty env) fields in
  let rec lower env = function
    | (Var _ | Const _ | Aaccess _) as expr -> expr
    | App(callee,args) -> App(lower env callee,List.map(lower env)args)
    | Prim(op,args) -> Prim((match op with Cast ty -> Cast(lower_type ty) | _ -> op),List.map(lower env)args)
    | Let(name,ty,first,body) -> Let(name,lower_type ty,lower env first,lower(TC.Env.add name ty env)body)
    | If(a,b,c) -> If(lower env a,lower env b,lower env c)
    | For(a,b,dir,c) -> For(lower env a,lower env b,dir,lower env c)
    | Sinit(name,fields,values) -> Sinit(name,fields,List.map(lower env)values)
    | Fget(value,field) -> Fget(lower env value,field)
    | Ainit(name,values) -> Ainit(name,List.map(lower env)values)
    | Esome value ->
        (match infer env value with
        | Ptr(Otype _ as inner) ->
            let name,tag,payload = representation (Otype inner) in
            let tmp = fresh "some" in
            Let(tmp,lower_type(Ptr inner),lower env value,
              Sinit(name,[tag;payload],[tag_value true;Var tmp]))
        | Ptr _ -> Esome(lower env value)
        | _ -> raise (TC.TypeError "some expects a pointer type"))
    | Enone ty ->
        (match ty with Ptr(Otype _ as inner) -> absent(Otype inner)
        | Ptr _ -> Enone(lower_type ty)
        | _ -> raise (TC.TypeError "none expects a pointer type"))
    | Match(value,patterns,branches) ->
        let scrutinee_type = infer env value in
        (match scrutinee_type with
        | Ptr(Otype(Otype _ as inner) as pt) ->
            let _,tag,payload = representation pt in
            let tmp = fresh "match" in
            let some_branch = ref None and none_branch = ref None in
            List.iter2 (fun pattern body -> match pattern with
              | Psome name -> some_branch := Some(name,lower(branch_env env scrutinee_type pattern)body)
              | Pnone -> none_branch := Some(lower env body)
              | Pbytes _ -> raise(TC.TypeError "Cannot mix bytes and option match patterns")) patterns branches;
            (match !some_branch,!none_branch with
            | Some(name,yes),Some no ->
                let some = Let(name,lower_type(Ptr inner),Fget(Var tmp,payload),yes) in
                let condition,first,second = match patterns with
                  | Pnone :: _ -> Prim(Bop Oeq,[Fget(Var tmp,tag);tag_value false]),no,some
                  | _ -> Prim(Bop One,[Fget(Var tmp,tag);tag_value false]),some,no in
                Let(tmp,lower_type(Ptr pt),lower env value,If(condition,first,second))
            | _ -> raise(TC.TypeError "Option match requires some and none branches"))
        | _ -> Match(lower env value,List.map lower_pattern patterns,
            List.map2(fun pattern body -> lower(branch_env env scrutinee_type pattern)body)patterns branches)) in
  let lower_binding (name,ty) = name,lower_type ty in
  let lower_function (Tfundecl(name,result,effects,args,locals,body)) =
    let env = add_bindings globals (args @ locals) in
    Tfundecl(name,lower_type result,effects,List.map lower_binding args,
      List.map lower_binding locals,lower env body) in
  let lowered = List.map (function
    | Internal(fn,section) -> Internal(lower_function fn,section)
    | EBPFInternal(fn,section) -> EBPFInternal(lower_function fn,section)
    | StructDecl(name,fields,section) -> StructDecl(name,List.map lower_binding fields,section)
    | GlobalLet(name,ty,value,section) -> GlobalLet(name,lower_type ty,lower globals value,section)) program in
  List.rev !declarations @ lowered
