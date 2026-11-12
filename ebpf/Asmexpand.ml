(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the eBPF assembly code. *)

open Asm
open Asmexpandaux
open AST
open Camlcoq

exception Error of string

let ra = R9
let sp = R10

let warchi = if Archi.ptr64 then W64 else W32


let chunk_of_pointer = if Archi.ptr64 then DBWord else Word

(* Expansion of instructions *)
let current_frame_size = ref BinNums.Z0

let expand_alloc_frame sz ofs_ra ofs_link = current_frame_size := sz

let expand_free_frame sz ofs_ra ofs_link = ()


(* This static expansion belongs to the existing unverified pseudo-instruction
   expansion boundary.  Asmgen's Qed simulation retains Pbuiltin semantics;
   it does not claim a new memcpy-to-machine-instructions refinement proof. *)
let memcpy_arg = function
  | BA (IR r) ->
      let reg = match r with
        | R0 -> Machregs.I0 | R1 -> Machregs.I1 | R2 -> Machregs.I2
        | R3 -> Machregs.I3 | R4 -> Machregs.I4 | R5 -> Machregs.I5
        | R6 -> Machregs.I6 | R7 -> Machregs.I7 | R8 -> Machregs.I8
        | R9 -> Machregs.I9
        | R10 | BP -> raise (Error "Unsupported memcpy register argument") in
      BA reg
  | BA_addrstack ofs -> BA_addrstack ofs
  | _ -> raise (Error "Memcpy requires register or stack addresses")

let expand_memcpy size alignment args result =
  match result with
  | BR_none ->
      begin match Asmgen.transl_memcpy !current_frame_size size alignment
          (List.map memcpy_arg args) BR_none [] with
      | Errors.OK instructions -> List.iter emit instructions
      | Errors.Error _ -> raise (Error "Unsupported eBPF memcpy size, alignment, or offsets")
      end
  | _ -> raise (Error "Memcpy must not return a value")

let expand_instruction instr =
  match instr with
  | Pbuiltin (EF_memcpy (size, alignment), args, result) -> expand_memcpy size alignment args result
  | Pbuiltin _ -> raise (Error "Builtin is not supported by eBPF")
  | Pallocframe(sz,ofs_ra,ofs_link) -> expand_alloc_frame sz ofs_ra ofs_link
  | Pfreeframe(sz,ofs_ra,ofs_link)  -> expand_free_frame sz ofs_ra ofs_link
  | Pcmp(cmp,w,reg,regimm) ->
    (* reg := reg cmp regimm *)
    Datatypes.(
      let label_true = new_label () in
      let label_end   = new_label () in 
      (* if reg cmp regimm Goto goto_true *)
      emit (Pjmpcmp(cmp,w,reg,regimm, label_true));
      (* else reg := false *)
      emit (Palu(MOV,W64,reg, Coq_inr Integers.Int.zero));
      emit (Pjmp (Coq_inl label_end));
      emit (Plabel label_true);
      emit  (Palu(MOV,W64,reg, Coq_inr Integers.Int.one));
    emit (Plabel label_end))
  | _ -> emit instr


(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)

let int_reg_to_dwarf = function
               | R0  -> 1  | R1  -> 2  | R2  -> 3
   | R3  -> 4  | R4  -> 5  | R5  -> 6  | R6  -> 7
   | R7  -> 8  | R8  -> 9  | R9  -> 10 | R10 -> 11
   | BP  -> assert false


let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | _ -> assert false

(* The kernel supplies only R1 and R10 at entry. CompCert's ordinary calling
   convention spills incoming callee-saved registers when a helper call keeps
   values live. Give those otherwise undefined entry values a concrete value
   before their spill. Ordinary subprograms must preserve their caller's values. *)
let initialize_entry_registers id code =
  let entry = List.exists (function
    | Sections.Section_user (name, _, _) ->
        List.mem name ["xdp"; "socket"; "tc"; "cgroup/sock_create"; "raw_tracepoint/sys_enter"]
    | _ -> false) (C2C.atom_sections id) in
  if not entry then code else
  let spilled r = List.exists (function
    | Pstore (_, R10, Datatypes.Coq_inl src, _) -> src = r
    | _ -> false) code in
  let regs = List.filter spilled [R6; R7; R8; R9] in
  List.map (fun r -> Palu (MOV, W64, r, Datatypes.Coq_inr Integers.Int.zero)) regs
  @ code

let expand_function id fn =
  try
    current_frame_size := BinNums.Z0;
    set_current_function fn;
    expand id (int_reg_to_dwarf R10) preg_to_dwarf expand_instruction
      (initialize_entry_registers id fn.fn_code);
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
