(* Restricted typed maps: uint32 keys and ulong values, with modern BTF metadata.
   Handles are opaque at source level; their array representation is internal. *)
open Beepl_ast

type declaration = { name: string; kind: int; capacity: int }
let declarations : declaration list ref = ref []
let handle_type = Atype (Vtype Tuint32, 8)
let section_name = function
  | None -> ""
  | Some s ->
      let s = String.trim s in
      let s = if String.length s >= 8 && String.sub s 0 8 = "#section"
              then String.trim (String.sub s 8 (String.length s - 8)) else s in
      String.trim s
let is_map_section s = section_name s = ".maps"
let is_handle name = List.exists (fun m -> m.name = name) !declarations
let helper name = List.mem name ["bpf_map_lookup_elem"; "bpf_map_update_elem"; "bpf_map_delete_elem"]
let fail s = invalid_arg ("Map declaration/use: " ^ s)

let prepare prog =
  declarations := [];
  List.iter (function
    | StructDecl (name, fields, sec) when is_map_section sec ->
        if is_handle name then fail "duplicate map name";
        let kind, capacity = match fields with
          | [("map_type", Atype (Vtype Tuint32, k)); ("key", Vtype Tuint32);
             ("value", Vtype Tulong); ("max_entries", Atype (Vtype Tuint32, n))]
             when List.mem k [1; 2; 6] && n > 0 && n <= 65536 -> k, n
          | _ -> fail "expected map_type:uint32[1|2|6], key:uint32, value:ulong, max_entries:uint32[1..65536] in that order"
        in
        declarations := !declarations @ [{name; kind; capacity}]
    | GlobalLet (_, _, _, sec) when is_map_section sec -> fail "use a typed struct declaration in .maps"
    | _ -> ()) prog;
  let binding name = if is_handle name then fail "map handles cannot be shadowed" in
  let rec expr = function
    | App (Var f, Var m :: rest) when helper f ->
        if not (is_handle m) then fail "helper requires a declared map handle";
        List.iter expr rest
    | App (Var f, _) when helper f -> fail "helper requires a named map handle"
    | Var m | Aaccess (m, _) when is_handle m -> fail "map handles may only be passed directly to map helpers"
    | App (f, es) -> expr f; List.iter expr es
    | Prim (_, es) | Sinit (_, _, es) | Ainit (_, es) -> List.iter expr es
    | Let (x, _, a, b) -> binding x; expr a; expr b
    | If (a,b,c) | For (a,b,_,c) -> expr a; expr b; expr c
    | Fget (e,_) | Esome e -> expr e
    | Match (e, ps, es) -> expr e;
        List.iter (function Psome x -> binding x | Pbytes (x,_,xs) -> binding x; List.iter (fun (x,_) -> binding x) xs | _ -> ()) ps;
        List.iter expr es
    | Var _ | Const _ | Aaccess _ | Enone _ -> ()
  in
  List.iter (function
    | Internal (Tfundecl (name,_,_,args,vars,body),_)
    | EBPFInternal (Tfundecl (name,_,_,args,vars,body),_) ->
        binding name; List.iter (fun (n,_) -> binding n) (args @ vars); expr body
    | GlobalLet (name,_,e,_) -> binding name; expr e
    | _ -> ()) prog

(* Emit BTF INT, PTR, ARRAY, STRUCT, VAR and DATASEC types. LLVM assembles
   relocatable DATASEC offsets; libbpf reads this metadata without legacy maps. *)
let emit_btf oc =
  if !declarations <> [] then begin
    let strings = Buffer.create 128 in
    Buffer.add_char strings '\000';
    let str s = let n = Buffer.length strings in Buffer.add_string strings s; Buffer.add_char strings '\000'; n in
    let types = Buffer.create 512 in
    let next = ref 0 in
    let word n = Buffer.add_string types (Printf.sprintf "\t.long %d\n" n) in
    let typ name kind count size extra =
      incr next; word (if name = "" then 0 else str name);
      word ((kind lsl 24) lor count); word size; List.iter word extra; !next in
    let u32 = typ "uint32" 1 0 4 [32] in
    let u64 = typ "ulong" 1 0 8 [64] in
    let keyptr = typ "" 2 0 u32 [] in
    let valptr = typ "" 2 0 u64 [] in
    let vars = List.map (fun m ->
      let ka = typ "" 3 0 0 [u32;u32;m.kind] in
      let kp = typ "" 2 0 ka [] in
      let ca = typ "" 3 0 0 [u32;u32;m.capacity] in
      let cp = typ "" 2 0 ca [] in
      let st = typ "" 4 4 32 [str "type";kp;0; str "key";keyptr;64;
                               str "value";valptr;128; str "max_entries";cp;192] in
      let v = typ m.name 14 0 st [1] in (m.name,v)) !declarations in
    ignore (typ ".maps" 15 (List.length vars) 0 []);
    List.iter (fun (name,v) -> word v; Buffer.add_string types ("\t.long " ^ name ^ "\n"); word 32) vars;
    Printf.fprintf oc "\n\t.section .BTF,\"\",@progbits\n\t.short 0xeb9f\n\t.byte 1,0\n\t.long 24\n\t.long 0\n\t.long .Lbee_btf_types_end-.Lbee_btf_types\n\t.long .Lbee_btf_types_end-.Lbee_btf_types\n\t.long %d\n.Lbee_btf_types:\n%s.Lbee_btf_types_end:\n"
      (Buffer.length strings) (Buffer.contents types);
    String.iter (fun c -> Printf.fprintf oc "\t.byte %d\n" (Char.code c)) (Buffer.contents strings)
  end
