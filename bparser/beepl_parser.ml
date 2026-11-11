
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | XOR
    | WRITE
    | WITH
    | VARARG
    | UP
    | UNIT
    | ULONGTYPE
    | UINT8TYPE
    | UINT32TYPE
    | UINT16TYPE
    | TSTRUCT
    | TILDE
    | THEN
    | STRUCT
    | STRING of 
# 39 "bparser/beepl_parser.mly"
       (string)
# 29 "bparser/beepl_parser.ml"
  
    | STAR
    | SINIT
    | SHR
    | SHL
    | SECTION of 
# 40 "bparser/beepl_parser.mly"
       (string)
# 38 "bparser/beepl_parser.ml"
  
    | RULONGTYPE
    | RUINT8TYPE
    | RUINT32TYPE
    | RUINT16TYPE
    | RSTRUCT
    | RPAREN
    | RLONGTYPE
    | RINT8TYPE
    | RINT32TYPE
    | RINT16TYPE
    | REF
    | READ
    | RBRACK
    | RBRACE
    | RBOOLTYPE
    | RAULONG
    | RAUINT8
    | RAUINT32
    | RAUINT16
    | RARRAY
    | RALONG
    | RAINT8
    | RAINT32
    | RAINT16
    | RABOOL
    | PLUS
    | PBYTES
    | OSOME
    | ORULONGTYPE
    | ORUINT8TYPE
    | ORUINT32TYPE
    | ORUINT16TYPE
    | ORSTRUCT
    | ORLONGTYPE
    | ORINT8TYPE
    | ORINT32TYPE
    | ORINT16TYPE
    | ORBOOLTYPE
    | ORAULONG
    | ORAUINT8
    | ORAUINT32
    | ORAUINT16
    | ORARRAY
    | ORALONG
    | ORAINT8
    | ORAINT32
    | ORAINT16
    | ORABOOL
    | OR
    | ONONE
    | OEQ
    | NOVARARG
    | NEQ
    | NEG
    | MUL
    | MOD
    | MINUS
    | MATCH
    | MASSGN
    | LT
    | LPAREN
    | LONGTYPE
    | LET
    | LE
    | LBRACK
    | LBRACE
    | IO
    | INT8TYPE
    | INT64 of 
# 7 "bparser/beepl_parser.mly"
       (int64)
# 111 "bparser/beepl_parser.ml"
  
    | INT32TYPE
    | INT32 of 
# 6 "bparser/beepl_parser.mly"
       (int32)
# 117 "bparser/beepl_parser.ml"
  
    | INT16TYPE
    | IN
    | IF
    | IDENT of 
# 5 "bparser/beepl_parser.mly"
       (string)
# 125 "bparser/beepl_parser.ml"
  
    | HASHEBPF
    | GT
    | GE
    | FUNTYPE
    | FUNC
    | FOR
    | EQ
    | EOF
    | EMPTYBRACKETS
    | ELSE
    | DOWN
    | DOT
    | DIVERGENCE
    | DIV
    | DEREF
    | COMMA
    | COLON
    | CAST
    | BYTES
    | BOOLTYPE
    | BOOL of 
# 8 "bparser/beepl_parser.mly"
       (bool)
# 150 "bparser/beepl_parser.ml"
  
    | BAR
    | ARROW
    | ARRAY
    | AND
    | ALLOC
    | AINIT
    | AACEESS
  
end

include MenhirBasics

# 1 "bparser/beepl_parser.mly"
  
open Beepl_ast

# 168 "bparser/beepl_parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_prog) _menhir_state
    (** State 000.
        Stack shape : <empty>.
        Start symbol: prog. *)

  | MenhirState001 : (('s, _menhir_box_prog) _menhir_cell1_SECTION, _menhir_box_prog) _menhir_state
    (** State 001.
        Stack shape : SECTION.
        Start symbol: prog. *)

  | MenhirState002 : (('s, _menhir_box_prog) _menhir_cell1_HASHEBPF, _menhir_box_prog) _menhir_state
    (** State 002.
        Stack shape : HASHEBPF.
        Start symbol: prog. *)

  | MenhirState007 : (('s, _menhir_box_prog) _menhir_cell1_toplevel, _menhir_box_prog) _menhir_state
    (** State 007.
        Stack shape : toplevel.
        Start symbol: prog. *)

  | MenhirState012 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 012.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState014 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 014.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState116 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 116.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState123 : (('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_state
    (** State 123.
        Stack shape : FUNTYPE.
        Start symbol: prog. *)

  | MenhirState127 : (('s, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 127.
        Stack shape : typ.
        Start symbol: prog. *)

  | MenhirState130 : (('s, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 130.
        Stack shape : typ.
        Start symbol: prog. *)

  | MenhirState135 : ((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_state
    (** State 135.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)).
        Start symbol: prog. *)

  | MenhirState143 : (((('s, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_beepl_effect__, _menhir_box_prog) _menhir_state
    (** State 143.
        Stack shape : FUNTYPE loption(separated_nonempty_list(COMMA,typ)) loption(separated_nonempty_list(COMMA,beepl_effect)).
        Start symbol: prog. *)

  | MenhirState150 : (('s, _menhir_box_prog) _menhir_cell1_beepl_effect, _menhir_box_prog) _menhir_state
    (** State 150.
        Stack shape : beepl_effect.
        Start symbol: prog. *)

  | MenhirState157 : (('s, _menhir_box_prog) _menhir_cell1_field_decl, _menhir_box_prog) _menhir_state
    (** State 157.
        Stack shape : field_decl.
        Start symbol: prog. *)

  | MenhirState161 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 161.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState163 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 163.
        Stack shape : annotations IDENT typ.
        Start symbol: prog. *)

  | MenhirState165 : (('s, _menhir_box_prog) _menhir_cell1_TILDE, _menhir_box_prog) _menhir_state
    (** State 165.
        Stack shape : TILDE.
        Start symbol: prog. *)

  | MenhirState168 : (('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 168.
        Stack shape : STRUCT IDENT.
        Start symbol: prog. *)

  | MenhirState170 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 170.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState174 : ((('s, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_, _menhir_box_prog) _menhir_state
    (** State 174.
        Stack shape : STRUCT IDENT separated_nonempty_list(COMMA,IDENT).
        Start symbol: prog. *)

  | MenhirState176 : (('s, _menhir_box_prog) _menhir_cell1_REF, _menhir_box_prog) _menhir_state
    (** State 176.
        Stack shape : REF.
        Start symbol: prog. *)

  | MenhirState177 : (('s, _menhir_box_prog) _menhir_cell1_OSOME, _menhir_box_prog) _menhir_state
    (** State 177.
        Stack shape : OSOME.
        Start symbol: prog. *)

  | MenhirState178 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 178.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState180 : (('s, _menhir_box_prog) _menhir_cell1_MINUS, _menhir_box_prog) _menhir_state
    (** State 180.
        Stack shape : MINUS.
        Start symbol: prog. *)

  | MenhirState181 : (('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_state
    (** State 181.
        Stack shape : MATCH.
        Start symbol: prog. *)

  | MenhirState182 : (('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 182.
        Stack shape : LPAREN.
        Start symbol: prog. *)

  | MenhirState186 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_state
    (** State 186.
        Stack shape : LPAREN LPAREN.
        Start symbol: prog. *)

  | MenhirState189 : (('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 189.
        Stack shape : LET IDENT.
        Start symbol: prog. *)

  | MenhirState191 : ((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 191.
        Stack shape : LET IDENT typ.
        Start symbol: prog. *)

  | MenhirState192 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE, _menhir_box_prog) _menhir_state
    (** State 192.
        Stack shape : LET IDENT typ LBRACE.
        Start symbol: prog. *)

  | MenhirState195 : (('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_state
    (** State 195.
        Stack shape : IF.
        Start symbol: prog. *)

  | MenhirState201 : (('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_state
    (** State 201.
        Stack shape : FOR.
        Start symbol: prog. *)

  | MenhirState202 : (('s, _menhir_box_prog) _menhir_cell1_DEREF, _menhir_box_prog) _menhir_state
    (** State 202.
        Stack shape : DEREF.
        Start symbol: prog. *)

  | MenhirState205 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 205.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState210 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 210.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState212 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 212.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState214 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 214.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState216 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 216.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState221 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 221.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState223 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 223.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState225 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 225.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState227 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 227.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState229 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 229.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState231 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 231.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState233 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 233.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState235 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 235.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState237 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 237.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState239 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 239.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState241 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 241.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState243 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 243.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState245 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 245.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState247 : (('s, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 247.
        Stack shape : expr.
        Start symbol: prog. *)

  | MenhirState250 : ((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 250.
        Stack shape : FOR expr.
        Start symbol: prog. *)

  | MenhirState256 : (((('s, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir, _menhir_box_prog) _menhir_state
    (** State 256.
        Stack shape : FOR expr expr dir.
        Start symbol: prog. *)

  | MenhirState260 : ((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 260.
        Stack shape : IF expr.
        Start symbol: prog. *)

  | MenhirState262 : (((('s, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 262.
        Stack shape : IF expr expr.
        Start symbol: prog. *)

  | MenhirState268 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_state
    (** State 268.
        Stack shape : LET IDENT typ expr.
        Start symbol: prog. *)

  | MenhirState271 : (((('s, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems, _menhir_box_prog) _menhir_state
    (** State 271.
        Stack shape : LET IDENT typ array_elems.
        Start symbol: prog. *)

  | MenhirState274 : ((('s, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 274.
        Stack shape : LPAREN typ.
        Start symbol: prog. *)

  | MenhirState281 : ((('s, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_, _menhir_box_prog) _menhir_state
    (** State 281.
        Stack shape : MATCH expr option(BAR).
        Start symbol: prog. *)

  | MenhirState284 : (('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 284.
        Stack shape : PBYTES IDENT.
        Start symbol: prog. *)

  | MenhirState286 : ((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 286.
        Stack shape : PBYTES IDENT typ.
        Start symbol: prog. *)

  | MenhirState289 : (('s, _menhir_box_prog) _menhir_cell1_IDENT, _menhir_box_prog) _menhir_state
    (** State 289.
        Stack shape : IDENT.
        Start symbol: prog. *)

  | MenhirState295 : (('s, _menhir_box_prog) _menhir_cell1_bytes_field, _menhir_box_prog) _menhir_state
    (** State 295.
        Stack shape : bytes_field.
        Start symbol: prog. *)

  | MenhirState299 : ((('s, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ _menhir_cell0_bytes_fields, _menhir_box_prog) _menhir_state
    (** State 299.
        Stack shape : PBYTES IDENT typ bytes_fields.
        Start symbol: prog. *)

  | MenhirState303 : (('s, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 303.
        Stack shape : OSOME IDENT.
        Start symbol: prog. *)

  | MenhirState306 : (('s, _menhir_box_prog) _menhir_cell1_ONONE, _menhir_box_prog) _menhir_state
    (** State 306.
        Stack shape : ONONE.
        Start symbol: prog. *)

  | MenhirState310 : (('s, _menhir_box_prog) _menhir_cell1_clause, _menhir_box_prog) _menhir_state
    (** State 310.
        Stack shape : clause.
        Start symbol: prog. *)

  | MenhirState321 : (('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_state
    (** State 321.
        Stack shape : annotations IDENT.
        Start symbol: prog. *)

  | MenhirState327 : ((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_state
    (** State 327.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)).
        Start symbol: prog. *)

  | MenhirState329 : (((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_state
    (** State 329.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ.
        Start symbol: prog. *)

  | MenhirState333 : ((((('s, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list, _menhir_box_prog) _menhir_state
    (** State 333.
        Stack shape : annotations IDENT loption(separated_nonempty_list(COMMA,arg)) typ effect_list.
        Start symbol: prog. *)

  | MenhirState337 : (('s, _menhir_box_prog) _menhir_cell1_arg, _menhir_box_prog) _menhir_state
    (** State 337.
        Stack shape : arg.
        Start symbol: prog. *)


and ('s, 'r) _menhir_cell1_annotations = 
  | MenhirCell1_annotations of 's * ('s, 'r) _menhir_state * (bool * string option)

and ('s, 'r) _menhir_cell1_arg = 
  | MenhirCell1_arg of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_array_elems = 
  | MenhirCell1_array_elems of 's * ('s, 'r) _menhir_state * (Beepl_ast.expr list)

and ('s, 'r) _menhir_cell1_beepl_effect = 
  | MenhirCell1_beepl_effect of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect)

and ('s, 'r) _menhir_cell1_bytes_field = 
  | MenhirCell1_bytes_field of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and 's _menhir_cell0_bytes_fields = 
  | MenhirCell0_bytes_fields of 's * ((string * Beepl_ast.typ) list)

and ('s, 'r) _menhir_cell1_clause = 
  | MenhirCell1_clause of 's * ('s, 'r) _menhir_state * (Beepl_ast.pattern * Beepl_ast.expr)

and 's _menhir_cell0_dir = 
  | MenhirCell0_dir of 's * (Beepl_ast.dir)

and ('s, 'r) _menhir_cell1_effect_list = 
  | MenhirCell1_effect_list of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect list)

and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * (Beepl_ast.expr)

and ('s, 'r) _menhir_cell1_field_decl = 
  | MenhirCell1_field_decl of 's * ('s, 'r) _menhir_state * (string * Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ of 's * ('s, 'r) _menhir_state * ((string * Beepl_ast.typ) list)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_beepl_effect__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_beepl_effect__ of 's * ('s, 'r) _menhir_state * (Beepl_ast.effect list)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ of 's * ('s, 'r) _menhir_state * (Beepl_ast.typ list)

and 's _menhir_cell0_option_BAR_ = 
  | MenhirCell0_option_BAR_ of 's * (unit option)

and ('s, 'r) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_ = 
  | MenhirCell1_separated_nonempty_list_COMMA_IDENT_ of 's * ('s, 'r) _menhir_state * (string list)

and ('s, 'r) _menhir_cell1_toplevel = 
  | MenhirCell1_toplevel of 's * ('s, 'r) _menhir_state * (Beepl_ast.toplevel)

and ('s, 'r) _menhir_cell1_typ = 
  | MenhirCell1_typ of 's * ('s, 'r) _menhir_state * (Beepl_ast.typ)

and ('s, 'r) _menhir_cell1_DEREF = 
  | MenhirCell1_DEREF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FOR = 
  | MenhirCell1_FOR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FUNTYPE = 
  | MenhirCell1_FUNTYPE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_HASHEBPF = 
  | MenhirCell1_HASHEBPF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IDENT = 
  | MenhirCell1_IDENT of 's * ('s, 'r) _menhir_state * 
# 5 "bparser/beepl_parser.mly"
       (string)
# 607 "bparser/beepl_parser.ml"


and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * 
# 5 "bparser/beepl_parser.mly"
       (string)
# 614 "bparser/beepl_parser.ml"


and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACE = 
  | MenhirCell1_LBRACE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MATCH = 
  | MenhirCell1_MATCH of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_MINUS = 
  | MenhirCell1_MINUS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ONONE = 
  | MenhirCell1_ONONE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_OSOME = 
  | MenhirCell1_OSOME of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PBYTES = 
  | MenhirCell1_PBYTES of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_REF = 
  | MenhirCell1_REF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SECTION = 
  | MenhirCell1_SECTION of 's * ('s, 'r) _menhir_state * 
# 40 "bparser/beepl_parser.mly"
       (string)
# 651 "bparser/beepl_parser.ml"


and ('s, 'r) _menhir_cell1_STRUCT = 
  | MenhirCell1_STRUCT of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_TILDE = 
  | MenhirCell1_TILDE of 's * ('s, 'r) _menhir_state

and _menhir_box_prog = 
  | MenhirBox_prog of (Beepl_ast.program) [@@unboxed]

let _menhir_action_001 =
  fun rest ->
    (
# 93 "bparser/beepl_parser.mly"
                                    ( let (is_ebpf, section) = rest in (true, section) )
# 668 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_002 =
  fun rest secname ->
    (
# 94 "bparser/beepl_parser.mly"
                                             ( let (is_ebpf, _) = rest in (is_ebpf, Some secname) )
# 676 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_003 =
  fun () ->
    (
# 95 "bparser/beepl_parser.mly"
                ( (false, None) )
# 684 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_004 =
  fun anns ->
    (
# 90 "bparser/beepl_parser.mly"
                           ( anns )
# 692 "bparser/beepl_parser.ml"
     : (bool * string option))

let _menhir_action_005 =
  fun id t ->
    (
# 102 "bparser/beepl_parser.mly"
                       ( (id, t) )
# 700 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_006 =
  fun xs ->
    let xs = 
# 241 "<standard.mly>"
    ( xs )
# 708 "bparser/beepl_parser.ml"
     in
    (
# 188 "bparser/beepl_parser.mly"
                                                   ( xs )
# 713 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_007 =
  fun () ->
    (
# 108 "bparser/beepl_parser.mly"
               ( Divergence )
# 721 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_008 =
  fun () ->
    (
# 109 "bparser/beepl_parser.mly"
         ( Read )
# 729 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_009 =
  fun () ->
    (
# 110 "bparser/beepl_parser.mly"
          ( Write )
# 737 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_010 =
  fun () ->
    (
# 111 "bparser/beepl_parser.mly"
          ( Alloc )
# 745 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_011 =
  fun () ->
    (
# 112 "bparser/beepl_parser.mly"
       ( Io )
# 753 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect))

let _menhir_action_012 =
  fun id t ->
    (
# 191 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 761 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_013 =
  fun () ->
    (
# 195 "bparser/beepl_parser.mly"
                                                   ( [] )
# 769 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_014 =
  fun () ->
    (
# 197 "bparser/beepl_parser.mly"
                                                   ( [] )
# 777 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_015 =
  fun xs ->
    let xs = 
# 241 "<standard.mly>"
    ( xs )
# 785 "bparser/beepl_parser.ml"
     in
    (
# 199 "bparser/beepl_parser.mly"
                                                           ( xs )
# 790 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_016 =
  fun e id ->
    (
# 220 "bparser/beepl_parser.mly"
                                 ( (Psome id, e) )
# 798 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_017 =
  fun e ->
    (
# 221 "bparser/beepl_parser.mly"
                                 ( (Pnone   , e) )
# 806 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_018 =
  fun e fields id t ->
    (
# 224 "bparser/beepl_parser.mly"
    ( (Pbytes (id, t, fields), e) )
# 814 "bparser/beepl_parser.ml"
     : (Beepl_ast.pattern * Beepl_ast.expr))

let _menhir_action_019 =
  fun b ->
    (
# 181 "bparser/beepl_parser.mly"
             ( Cbool b )
# 822 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_020 =
  fun () ->
    (
# 182 "bparser/beepl_parser.mly"
             ( Cunit )
# 830 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_021 =
  fun i ->
    (
# 183 "bparser/beepl_parser.mly"
              ( Cint32 i )
# 838 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_022 =
  fun l ->
    (
# 184 "bparser/beepl_parser.mly"
              ( Clong l )
# 846 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_023 =
  fun s ->
    (
# 185 "bparser/beepl_parser.mly"
               ( Cstring s )
# 854 "bparser/beepl_parser.ml"
     : (Beepl_ast.const))

let _menhir_action_024 =
  fun () ->
    (
# 177 "bparser/beepl_parser.mly"
         ( Up )
# 862 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_025 =
  fun () ->
    (
# 178 "bparser/beepl_parser.mly"
         ( Down )
# 870 "bparser/beepl_parser.ml"
     : (Beepl_ast.dir))

let _menhir_action_026 =
  fun () ->
    (
# 98 "bparser/beepl_parser.mly"
                  ( [] )
# 878 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_027 =
  fun _1 ->
    (
# 99 "bparser/beepl_parser.mly"
                                                 ( _1 )
# 886 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_028 =
  fun _2 ->
    (
# 227 "bparser/beepl_parser.mly"
                                ( _2 )
# 894 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_029 =
  fun id ->
    (
# 228 "bparser/beepl_parser.mly"
               ( Var id )
# 902 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_030 =
  fun c ->
    (
# 229 "bparser/beepl_parser.mly"
               ( Const c )
# 910 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_031 =
  fun e ->
    (
# 232 "bparser/beepl_parser.mly"
    ( Prim (Uop UOverloadTilde, [e]) )
# 918 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_032 =
  fun e ->
    (
# 234 "bparser/beepl_parser.mly"
    ( Prim (Uop Oneg, [e]) )
# 926 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_033 =
  fun e1 e2 ->
    (
# 237 "bparser/beepl_parser.mly"
    ( Prim (Bop Oadd, [e1; e2]) )
# 934 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_034 =
  fun e1 e2 ->
    (
# 239 "bparser/beepl_parser.mly"
    ( Prim (Bop Osub, [e1; e2]) )
# 942 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_035 =
  fun e1 e2 ->
    (
# 241 "bparser/beepl_parser.mly"
    ( Prim (Bop Omul, [e1; e2]) )
# 950 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_036 =
  fun e1 e2 ->
    (
# 243 "bparser/beepl_parser.mly"
    ( Prim (Bop Odiv, [e1; e2]) )
# 958 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_037 =
  fun e1 e2 ->
    (
# 245 "bparser/beepl_parser.mly"
    ( Prim (Bop Omod, [e1; e2]) )
# 966 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_038 =
  fun e1 e2 ->
    (
# 247 "bparser/beepl_parser.mly"
    ( Prim (Bop Oand, [e1; e2]) )
# 974 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_039 =
  fun e1 e2 ->
    (
# 249 "bparser/beepl_parser.mly"
    ( Prim (Bop Oor, [e1; e2]) )
# 982 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_040 =
  fun e1 e2 ->
    (
# 251 "bparser/beepl_parser.mly"
    ( Prim (Bop Oxor, [e1; e2]) )
# 990 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_041 =
  fun e1 e2 ->
    (
# 253 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshl, [e1; e2]) )
# 998 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_042 =
  fun e1 e2 ->
    (
# 255 "bparser/beepl_parser.mly"
    ( Prim (Bop Oshr, [e1; e2]) )
# 1006 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_043 =
  fun e1 e2 ->
    (
# 257 "bparser/beepl_parser.mly"
    ( Prim (Bop Oeq, [e1; e2]) )
# 1014 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_044 =
  fun e1 e2 ->
    (
# 259 "bparser/beepl_parser.mly"
    ( Prim (Bop One, [e1; e2]) )
# 1022 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_045 =
  fun e1 e2 ->
    (
# 261 "bparser/beepl_parser.mly"
    ( Prim (Bop Olt, [e1; e2]) )
# 1030 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_046 =
  fun e1 e2 ->
    (
# 263 "bparser/beepl_parser.mly"
    ( Prim (Bop Ogt, [e1; e2]) )
# 1038 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_047 =
  fun e1 e2 ->
    (
# 265 "bparser/beepl_parser.mly"
    ( Prim (Bop Ole, [e1; e2]) )
# 1046 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_048 =
  fun e1 e2 ->
    (
# 267 "bparser/beepl_parser.mly"
    ( Prim (Bop Oge, [e1; e2]) )
# 1054 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_049 =
  fun e t ->
    (
# 269 "bparser/beepl_parser.mly"
    (Prim (Cast t, [e]) )
# 1062 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_050 =
  fun e ->
    (
# 271 "bparser/beepl_parser.mly"
    (Prim (Ref, [e]))
# 1070 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_051 =
  fun e ->
    (
# 273 "bparser/beepl_parser.mly"
    (Prim (Deref, [e]))
# 1078 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_052 =
  fun e1 e2 ->
    (
# 275 "bparser/beepl_parser.mly"
    ( Prim (Massgn, [e1; e2]) )
# 1086 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_053 =
  fun args fn ->
    (
# 278 "bparser/beepl_parser.mly"
    ( App(fn, args) )
# 1094 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_054 =
  fun fn ->
    (
# 280 "bparser/beepl_parser.mly"
    ( App(fn, []) )
# 1102 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_055 =
  fun e2 elems id t ->
    (
# 282 "bparser/beepl_parser.mly"
    ( 
      match t with
      | Atype (_, _) -> Let(id, t, Ainit(id, elems), e2)
      | _ -> failwith "Array initializer {..} can only initialize an array type"
    )
# 1114 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_056 =
  fun e1 e2 id t ->
    (
# 288 "bparser/beepl_parser.mly"
    ( Let(id, t, e1, e2) )
# 1122 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_057 =
  fun e1 e2 e3 ->
    (
# 290 "bparser/beepl_parser.mly"
    ( If(e1, e2, e3) )
# 1130 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_058 =
  fun d e1 e2 e3 ->
    (
# 292 "bparser/beepl_parser.mly"
    ( For(e1, e2, d, e3) )
# 1138 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_059 =
  fun args fields id ->
    (
# 295 "bparser/beepl_parser.mly"
    ( Sinit(id, fields, args) )
# 1146 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_060 =
  fun e id ->
    (
# 297 "bparser/beepl_parser.mly"
    ( Fget(e, id) )
# 1154 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_061 =
  fun id n ->
    (
# 299 "bparser/beepl_parser.mly"
    ( Aaccess(id, Int32.to_int n) )
# 1162 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_062 =
  fun cs e optbar ->
    (
# 301 "bparser/beepl_parser.mly"
    ( 
      let pats, bodies = List.split cs in
      Match(e, pats, bodies)
    )
# 1173 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_063 =
  fun e ->
    (
# 305 "bparser/beepl_parser.mly"
                   ( Esome e )
# 1181 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_064 =
  fun t ->
    (
# 306 "bparser/beepl_parser.mly"
                      ( Enone t)
# 1189 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr))

let _menhir_action_065 =
  fun id t ->
    (
# 105 "bparser/beepl_parser.mly"
                             ( (id, t) )
# 1197 "bparser/beepl_parser.ml"
     : (string * Beepl_ast.typ))

let _menhir_action_066 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1205 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_067 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1213 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_068 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1221 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_069 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1229 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_070 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1237 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_071 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1245 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_072 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1253 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_073 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1261 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_074 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1269 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_075 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1277 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_076 =
  fun () ->
    (
# 145 "<standard.mly>"
    ( [] )
# 1285 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_077 =
  fun x ->
    (
# 148 "<standard.mly>"
    ( x )
# 1293 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_078 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 1301 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_079 =
  fun x ->
    (
# 114 "<standard.mly>"
    ( Some x )
# 1309 "bparser/beepl_parser.ml"
     : (unit option))

let _menhir_action_080 =
  fun tops ->
    (
# 60 "bparser/beepl_parser.mly"
                             ( tops )
# 1317 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_081 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1325 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_082 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1333 "bparser/beepl_parser.ml"
     : ((Beepl_ast.pattern * Beepl_ast.expr) list))

let _menhir_action_083 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1341 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_084 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1349 "bparser/beepl_parser.ml"
     : (string list))

let _menhir_action_085 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1357 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_086 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1365 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_087 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1373 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_088 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1381 "bparser/beepl_parser.ml"
     : (Beepl_ast.effect list))

let _menhir_action_089 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1389 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_090 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1397 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_091 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1405 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_092 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1413 "bparser/beepl_parser.ml"
     : (Beepl_ast.expr list))

let _menhir_action_093 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1421 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_094 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1429 "bparser/beepl_parser.ml"
     : ((string * Beepl_ast.typ) list))

let _menhir_action_095 =
  fun x ->
    (
# 250 "<standard.mly>"
    ( [ x ] )
# 1437 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_096 =
  fun x xs ->
    (
# 253 "<standard.mly>"
    ( x :: xs )
# 1445 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ list))

let _menhir_action_097 =
  fun anns body effs id ret xs ->
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1453 "bparser/beepl_parser.ml"
     in
    (
# 69 "bparser/beepl_parser.mly"
    (
      let f = Tfundecl(id, ret, effs, args, [], body) in
      match anns with
      | (false, sec) -> Internal (f, sec)
      | (true, sec)  -> EBPFInternal (f, sec)
    )
# 1463 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_098 =
  fun anns id xs ->
    let fields = 
# 241 "<standard.mly>"
    ( xs )
# 1471 "bparser/beepl_parser.ml"
     in
    (
# 76 "bparser/beepl_parser.mly"
  (
    match anns with
    | (false, sec) -> StructDecl(id, fields, sec)
    | (true, _sec) -> failwith "Struct decl cannot be eBPF"
  )
# 1480 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_099 =
  fun anns e id t ->
    (
# 82 "bparser/beepl_parser.mly"
    (
      match anns with
      | (false, sec) -> GlobalLet(id, t, e, sec)
      | (true, sec)  -> failwith "Global let cannot be eBPF"
    )
# 1492 "bparser/beepl_parser.ml"
     : (Beepl_ast.toplevel))

let _menhir_action_100 =
  fun tl ->
    (
# 63 "bparser/beepl_parser.mly"
                  ( [tl] )
# 1500 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_101 =
  fun tl tlrest ->
    (
# 64 "bparser/beepl_parser.mly"
                                         ( tl :: tlrest )
# 1508 "bparser/beepl_parser.ml"
     : (Beepl_ast.program))

let _menhir_action_102 =
  fun () ->
    (
# 119 "bparser/beepl_parser.mly"
              ( Vtype Tbool )
# 1516 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_103 =
  fun () ->
    (
# 120 "bparser/beepl_parser.mly"
              ( Vtype Tuint8 )
# 1524 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_104 =
  fun () ->
    (
# 121 "bparser/beepl_parser.mly"
              ( Vtype Tint8 )
# 1532 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_105 =
  fun () ->
    (
# 122 "bparser/beepl_parser.mly"
               ( Vtype Tuint16 )
# 1540 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_106 =
  fun () ->
    (
# 123 "bparser/beepl_parser.mly"
              ( Vtype Tint16 )
# 1548 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_107 =
  fun () ->
    (
# 124 "bparser/beepl_parser.mly"
               ( Vtype Tuint32 )
# 1556 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_108 =
  fun () ->
    (
# 125 "bparser/beepl_parser.mly"
              ( Vtype Tint32 )
# 1564 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_109 =
  fun () ->
    (
# 126 "bparser/beepl_parser.mly"
              ( Vtype Tulong )
# 1572 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_110 =
  fun () ->
    (
# 127 "bparser/beepl_parser.mly"
              ( Vtype Tlong )
# 1580 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_111 =
  fun () ->
    (
# 128 "bparser/beepl_parser.mly"
                  ( Utype )
# 1588 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_112 =
  fun () ->
    (
# 129 "bparser/beepl_parser.mly"
              ( Utype )
# 1596 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_113 =
  fun () ->
    (
# 130 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tbool))) )
# 1604 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_114 =
  fun () ->
    (
# 131 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tint8))) )
# 1612 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_115 =
  fun () ->
    (
# 132 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tuint8))) )
# 1620 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_116 =
  fun () ->
    (
# 133 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tint16))) )
# 1628 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_117 =
  fun () ->
    (
# 134 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ((Bprim Tuint16))) )
# 1636 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_118 =
  fun () ->
    (
# 135 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tint32))) )
# 1644 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_119 =
  fun () ->
    (
# 136 "bparser/beepl_parser.mly"
                ( Ptr (Reftype ((Bprim Tuint32))) )
# 1652 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_120 =
  fun () ->
    (
# 137 "bparser/beepl_parser.mly"
              ( Ptr (Reftype ((Bprim Tlong))) )
# 1660 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_121 =
  fun () ->
    (
# 138 "bparser/beepl_parser.mly"
               ( Ptr (Reftype ((Bprim Tulong))) )
# 1668 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_122 =
  fun _2 ->
    (
# 139 "bparser/beepl_parser.mly"
                     ( Ptr (Reftype ((Bstruct _2))) )
# 1676 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_123 =
  fun n ->
    (
# 140 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ((Barray (Tbool, Int32.to_int n)))) )
# 1684 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_124 =
  fun n ->
    (
# 141 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ((Barray (Tint8, Int32.to_int n)))) )
# 1692 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_125 =
  fun n ->
    (
# 142 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ((Barray (Tuint8, Int32.to_int n)))) )
# 1700 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_126 =
  fun n ->
    (
# 143 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ((Barray (Tint16, Int32.to_int n)))) )
# 1708 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_127 =
  fun n ->
    (
# 144 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ((Barray (Tuint16, Int32.to_int n)))) )
# 1716 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_128 =
  fun n ->
    (
# 145 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ((Barray (Tint32, Int32.to_int n)))) )
# 1724 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_129 =
  fun n ->
    (
# 146 "bparser/beepl_parser.mly"
                                     ( Ptr (Reftype ((Barray (Tuint32, Int32.to_int n)))) )
# 1732 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_130 =
  fun n ->
    (
# 147 "bparser/beepl_parser.mly"
                                   ( Ptr (Reftype ((Barray (Tlong, Int32.to_int n)))) )
# 1740 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_131 =
  fun n ->
    (
# 148 "bparser/beepl_parser.mly"
                                    ( Ptr (Reftype ((Barray (Tulong, Int32.to_int n)))) )
# 1748 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_132 =
  fun () ->
    (
# 149 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tbool)))) )
# 1756 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_133 =
  fun () ->
    (
# 150 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tint8)))) )
# 1764 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_134 =
  fun () ->
    (
# 151 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tuint8)))) )
# 1772 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_135 =
  fun () ->
    (
# 152 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tint16)))) )
# 1780 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_136 =
  fun () ->
    (
# 153 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ((Bprim Tuint16)))) )
# 1788 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_137 =
  fun () ->
    (
# 154 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tint32)))) )
# 1796 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_138 =
  fun () ->
    (
# 155 "bparser/beepl_parser.mly"
                 ( Ptr (Otype (Reftype ((Bprim Tuint32)))) )
# 1804 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_139 =
  fun () ->
    (
# 156 "bparser/beepl_parser.mly"
               ( Ptr (Otype (Reftype ((Bprim Tlong)))) )
# 1812 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_140 =
  fun () ->
    (
# 157 "bparser/beepl_parser.mly"
                ( Ptr (Otype (Reftype ((Bprim Tulong)))) )
# 1820 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_141 =
  fun _2 ->
    (
# 158 "bparser/beepl_parser.mly"
                       ( Ptr (Otype (Reftype ((Bstruct _2)))) )
# 1828 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_142 =
  fun n ->
    (
# 159 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ((Barray (Tbool, Int32.to_int n))))) )
# 1836 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_143 =
  fun n ->
    (
# 160 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ((Barray (Tint8, Int32.to_int n))))) )
# 1844 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_144 =
  fun n ->
    (
# 161 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ((Barray (Tuint8, Int32.to_int n))))) )
# 1852 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_145 =
  fun n ->
    (
# 162 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ((Barray (Tint16, Int32.to_int n))))) )
# 1860 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_146 =
  fun n ->
    (
# 163 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ((Barray (Tuint16, Int32.to_int n))))) )
# 1868 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_147 =
  fun n ->
    (
# 164 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype (Reftype ((Barray (Tint32, Int32.to_int n))))) )
# 1876 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_148 =
  fun n ->
    (
# 165 "bparser/beepl_parser.mly"
                                      ( Ptr (Otype (Reftype ((Barray (Tuint32, Int32.to_int n))))) )
# 1884 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_149 =
  fun n ->
    (
# 166 "bparser/beepl_parser.mly"
                                    ( Ptr (Otype (Reftype ((Barray (Tlong, Int32.to_int n))))) )
# 1892 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_150 =
  fun n ->
    (
# 167 "bparser/beepl_parser.mly"
                                     ( Ptr (Otype ((Reftype ((Barray (Tulong, Int32.to_int n)))))) )
# 1900 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_151 =
  fun id ->
    (
# 168 "bparser/beepl_parser.mly"
                      ( Stype id )
# 1908 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_152 =
  fun n t ->
    (
# 169 "bparser/beepl_parser.mly"
                                    ( Atype(t, Int32.to_int n) )
# 1916 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_153 =
  fun ret va xs xs_inlined1 ->
    let eff =
      let xs = xs_inlined1 in
      
# 241 "<standard.mly>"
    ( xs )
# 1926 "bparser/beepl_parser.ml"
      
    in
    let args = 
# 241 "<standard.mly>"
    ( xs )
# 1932 "bparser/beepl_parser.ml"
     in
    (
# 171 "bparser/beepl_parser.mly"
                                                                                           ( Ftype(args, eff, ret, va) )
# 1937 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_154 =
  fun () ->
    (
# 172 "bparser/beepl_parser.mly"
          ( Bytes )
# 1945 "bparser/beepl_parser.ml"
     : (Beepl_ast.typ))

let _menhir_action_155 =
  fun () ->
    (
# 115 "bparser/beepl_parser.mly"
           ( true )
# 1953 "bparser/beepl_parser.ml"
     : (bool))

let _menhir_action_156 =
  fun () ->
    (
# 116 "bparser/beepl_parser.mly"
           ( false )
# 1961 "bparser/beepl_parser.ml"
     : (bool))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | XOR ->
        "XOR"
    | WRITE ->
        "WRITE"
    | WITH ->
        "WITH"
    | VARARG ->
        "VARARG"
    | UP ->
        "UP"
    | UNIT ->
        "UNIT"
    | ULONGTYPE ->
        "ULONGTYPE"
    | UINT8TYPE ->
        "UINT8TYPE"
    | UINT32TYPE ->
        "UINT32TYPE"
    | UINT16TYPE ->
        "UINT16TYPE"
    | TSTRUCT ->
        "TSTRUCT"
    | TILDE ->
        "TILDE"
    | THEN ->
        "THEN"
    | STRUCT ->
        "STRUCT"
    | STRING _ ->
        "STRING"
    | STAR ->
        "STAR"
    | SINIT ->
        "SINIT"
    | SHR ->
        "SHR"
    | SHL ->
        "SHL"
    | SECTION _ ->
        "SECTION"
    | RULONGTYPE ->
        "RULONGTYPE"
    | RUINT8TYPE ->
        "RUINT8TYPE"
    | RUINT32TYPE ->
        "RUINT32TYPE"
    | RUINT16TYPE ->
        "RUINT16TYPE"
    | RSTRUCT ->
        "RSTRUCT"
    | RPAREN ->
        "RPAREN"
    | RLONGTYPE ->
        "RLONGTYPE"
    | RINT8TYPE ->
        "RINT8TYPE"
    | RINT32TYPE ->
        "RINT32TYPE"
    | RINT16TYPE ->
        "RINT16TYPE"
    | REF ->
        "REF"
    | READ ->
        "READ"
    | RBRACK ->
        "RBRACK"
    | RBRACE ->
        "RBRACE"
    | RBOOLTYPE ->
        "RBOOLTYPE"
    | RAULONG ->
        "RAULONG"
    | RAUINT8 ->
        "RAUINT8"
    | RAUINT32 ->
        "RAUINT32"
    | RAUINT16 ->
        "RAUINT16"
    | RARRAY ->
        "RARRAY"
    | RALONG ->
        "RALONG"
    | RAINT8 ->
        "RAINT8"
    | RAINT32 ->
        "RAINT32"
    | RAINT16 ->
        "RAINT16"
    | RABOOL ->
        "RABOOL"
    | PLUS ->
        "PLUS"
    | PBYTES ->
        "PBYTES"
    | OSOME ->
        "OSOME"
    | ORULONGTYPE ->
        "ORULONGTYPE"
    | ORUINT8TYPE ->
        "ORUINT8TYPE"
    | ORUINT32TYPE ->
        "ORUINT32TYPE"
    | ORUINT16TYPE ->
        "ORUINT16TYPE"
    | ORSTRUCT ->
        "ORSTRUCT"
    | ORLONGTYPE ->
        "ORLONGTYPE"
    | ORINT8TYPE ->
        "ORINT8TYPE"
    | ORINT32TYPE ->
        "ORINT32TYPE"
    | ORINT16TYPE ->
        "ORINT16TYPE"
    | ORBOOLTYPE ->
        "ORBOOLTYPE"
    | ORAULONG ->
        "ORAULONG"
    | ORAUINT8 ->
        "ORAUINT8"
    | ORAUINT32 ->
        "ORAUINT32"
    | ORAUINT16 ->
        "ORAUINT16"
    | ORARRAY ->
        "ORARRAY"
    | ORALONG ->
        "ORALONG"
    | ORAINT8 ->
        "ORAINT8"
    | ORAINT32 ->
        "ORAINT32"
    | ORAINT16 ->
        "ORAINT16"
    | ORABOOL ->
        "ORABOOL"
    | OR ->
        "OR"
    | ONONE ->
        "ONONE"
    | OEQ ->
        "OEQ"
    | NOVARARG ->
        "NOVARARG"
    | NEQ ->
        "NEQ"
    | NEG ->
        "NEG"
    | MUL ->
        "MUL"
    | MOD ->
        "MOD"
    | MINUS ->
        "MINUS"
    | MATCH ->
        "MATCH"
    | MASSGN ->
        "MASSGN"
    | LT ->
        "LT"
    | LPAREN ->
        "LPAREN"
    | LONGTYPE ->
        "LONGTYPE"
    | LET ->
        "LET"
    | LE ->
        "LE"
    | LBRACK ->
        "LBRACK"
    | LBRACE ->
        "LBRACE"
    | IO ->
        "IO"
    | INT8TYPE ->
        "INT8TYPE"
    | INT64 _ ->
        "INT64"
    | INT32TYPE ->
        "INT32TYPE"
    | INT32 _ ->
        "INT32"
    | INT16TYPE ->
        "INT16TYPE"
    | IN ->
        "IN"
    | IF ->
        "IF"
    | IDENT _ ->
        "IDENT"
    | HASHEBPF ->
        "HASHEBPF"
    | GT ->
        "GT"
    | GE ->
        "GE"
    | FUNTYPE ->
        "FUNTYPE"
    | FUNC ->
        "FUNC"
    | FOR ->
        "FOR"
    | EQ ->
        "EQ"
    | EOF ->
        "EOF"
    | EMPTYBRACKETS ->
        "EMPTYBRACKETS"
    | ELSE ->
        "ELSE"
    | DOWN ->
        "DOWN"
    | DOT ->
        "DOT"
    | DIVERGENCE ->
        "DIVERGENCE"
    | DIV ->
        "DIV"
    | DEREF ->
        "DEREF"
    | COMMA ->
        "COMMA"
    | COLON ->
        "COLON"
    | CAST ->
        "CAST"
    | BYTES ->
        "BYTES"
    | BOOLTYPE ->
        "BOOLTYPE"
    | BOOL _ ->
        "BOOL"
    | BAR ->
        "BAR"
    | ARROW ->
        "ARROW"
    | ARRAY ->
        "ARRAY"
    | AND ->
        "AND"
    | ALLOC ->
        "ALLOC"
    | AINIT ->
        "AINIT"
    | AACEESS ->
        "AACEESS"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_005 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let tops = _v in
      let _v = _menhir_action_080 tops in
      MenhirBox_prog _v
  
  let rec _menhir_goto_toplevel_list : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState000 ->
          _menhir_run_005 _menhir_stack _v
      | MenhirState007 ->
          _menhir_run_008 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_008 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_toplevel -> _ -> _menhir_box_prog =
    fun _menhir_stack _v ->
      let MenhirCell1_toplevel (_menhir_stack, _menhir_s, tl) = _menhir_stack in
      let tlrest = _v in
      let _v = _menhir_action_101 tl tlrest in
      _menhir_goto_toplevel_list _menhir_stack _v _menhir_s
  
  let rec _menhir_run_001 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_SECTION (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v_0 ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState001
      | HASHEBPF ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState001
      | FUNC | LET | STRUCT ->
          let _v_1 = _menhir_action_003 () in
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_002 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState002
      | HASHEBPF ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState002
      | FUNC | LET | STRUCT ->
          let _v = _menhir_action_003 () in
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_003 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_HASHEBPF -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_HASHEBPF (_menhir_stack, _menhir_s) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_001 rest in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_annotation_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState002 ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState001 ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState000 ->
          _menhir_run_339 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState007 ->
          _menhir_run_339 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_004 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_SECTION -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_SECTION (_menhir_stack, _menhir_s, secname) = _menhir_stack in
      let rest = _v in
      let _v = _menhir_action_002 rest secname in
      _menhir_goto_annotation_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_339 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let anns = _v in
      let _v = _menhir_action_004 anns in
      let _menhir_stack = MenhirCell1_annotations (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STRUCT ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | LBRACE ->
                  let _menhir_s = MenhirState012 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | IDENT _v ->
                      _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | RBRACE ->
                      let _v = _menhir_action_074 () in
                      _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | LET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | COLON ->
                  let _menhir_s = MenhirState161 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | UNIT ->
                      _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ULONGTYPE ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT8TYPE ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT32TYPE ->
                      _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT16TYPE ->
                      _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | STRUCT ->
                      _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RULONGTYPE ->
                      _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT8TYPE ->
                      _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT32TYPE ->
                      _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT16TYPE ->
                      _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RLONGTYPE ->
                      _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT8TYPE ->
                      _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT32TYPE ->
                      _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT16TYPE ->
                      _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RBOOLTYPE ->
                      _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAULONG ->
                      _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT8 ->
                      _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT32 ->
                      _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT16 ->
                      _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RALONG ->
                      _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT8 ->
                      _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT32 ->
                      _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT16 ->
                      _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RABOOL ->
                      _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORSTRUCT ->
                      _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORLONGTYPE ->
                      _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT8TYPE ->
                      _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT32TYPE ->
                      _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT16TYPE ->
                      _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORBOOLTYPE ->
                      _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAULONG ->
                      _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT8 ->
                      _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT32 ->
                      _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT16 ->
                      _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORALONG ->
                      _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT8 ->
                      _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT32 ->
                      _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT16 ->
                      _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORABOOL ->
                      _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LPAREN ->
                      _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LONGTYPE ->
                      _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT8TYPE ->
                      _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT32TYPE ->
                      _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT16TYPE ->
                      _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | FUNTYPE ->
                      _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BYTES ->
                      _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BOOLTYPE ->
                      _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | FUNC ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | LPAREN ->
                  let _menhir_s = MenhirState321 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | UNIT ->
                      _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ULONGTYPE ->
                      _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT8TYPE ->
                      _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT32TYPE ->
                      _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | UINT16TYPE ->
                      _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | STRUCT ->
                      _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RULONGTYPE ->
                      _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT8TYPE ->
                      _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT32TYPE ->
                      _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RUINT16TYPE ->
                      _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RLONGTYPE ->
                      _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT8TYPE ->
                      _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT32TYPE ->
                      _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RINT16TYPE ->
                      _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RBOOLTYPE ->
                      _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAULONG ->
                      _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT8 ->
                      _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT32 ->
                      _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAUINT16 ->
                      _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RALONG ->
                      _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT8 ->
                      _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT32 ->
                      _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RAINT16 ->
                      _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RABOOL ->
                      _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORULONGTYPE ->
                      _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT8TYPE ->
                      _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT32TYPE ->
                      _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORUINT16TYPE ->
                      _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORSTRUCT ->
                      _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORLONGTYPE ->
                      _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT8TYPE ->
                      _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT32TYPE ->
                      _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORINT16TYPE ->
                      _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORBOOLTYPE ->
                      _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAULONG ->
                      _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT8 ->
                      _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT32 ->
                      _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAUINT16 ->
                      _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORALONG ->
                      _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT8 ->
                      _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT32 ->
                      _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORAINT16 ->
                      _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | ORABOOL ->
                      _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LPAREN ->
                      _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LONGTYPE ->
                      _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT8TYPE ->
                      _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT32TYPE ->
                      _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | INT16TYPE ->
                      _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | FUNTYPE ->
                      _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BYTES ->
                      _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | BOOLTYPE ->
                      _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RPAREN ->
                      let _v = _menhir_action_066 () in
                      _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_013 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState014 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_112 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_typ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState123 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState130 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState143 ->
          _menhir_run_144 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState014 ->
          _menhir_run_152 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState161 ->
          _menhir_run_162 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState178 ->
          _menhir_run_179 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState189 ->
          _menhir_run_190 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState182 ->
          _menhir_run_273 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState186 ->
          _menhir_run_273 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState284 ->
          _menhir_run_285 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState289 ->
          _menhir_run_290 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState321 ->
          _menhir_run_322 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState337 ->
          _menhir_run_322 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState327 ->
          _menhir_run_328 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_126 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState130 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_095 x in
          _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_127 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INT32 _v ->
          _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_128 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_typ (_menhir_stack, _menhir_s, t) = _menhir_stack in
          let n = _v in
          let _v = _menhir_action_152 n t in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_016 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_109 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_017 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_103 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_107 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_019 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_105 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_020 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer
          | AND | BAR | COMMA | DIV | DOT | ELSE | EMPTYBRACKETS | EOF | EQ | FUNC | GE | GT | HASHEBPF | IDENT _ | IN | LBRACK | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | NEQ | OEQ | OR | PLUS | RBRACE | RBRACK | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
              let id = _v in
              let _v = _menhir_action_151 id in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_022 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
      let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_122 _2 in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_023 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_121 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_024 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_115 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_025 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_119 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_026 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_117 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_027 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_120 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_028 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_114 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_029 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_118 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_030 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_116 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_031 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_113 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_032 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_131 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_036 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_125 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_040 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_129 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_044 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_127 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_048 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_130 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_124 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_056 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_128 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_060 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_126 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_064 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_123 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_068 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_140 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_069 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_134 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_070 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_138 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_071 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_136 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_072 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _2 = _v in
              let _v = _menhir_action_141 _2 in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_139 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_076 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_133 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_077 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_137 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_078 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_135 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_079 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_132 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_080 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_150 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_084 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_144 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_088 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_148 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_092 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_146 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_096 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_149 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_100 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_143 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_104 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_147 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_108 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_145 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_112 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACE ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let n = _v in
                  let _v = _menhir_action_142 n in
                  _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_116 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_117 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v = _menhir_action_111 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_118 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_110 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_119 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_104 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_120 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_108 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_121 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_106 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_122 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUNTYPE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState123 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RPAREN ->
              let _v = _menhir_action_076 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_124 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_154 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_125 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_102 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState135 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_140 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | COMMA ->
              let _v = _menhir_action_068 () in
              _menhir_goto_loption_separated_nonempty_list_COMMA_beepl_effect__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_136 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_009 () in
      _menhir_goto_beepl_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_beepl_effect : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_beepl_effect (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState150 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | READ ->
              _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IO ->
              _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DIVERGENCE ->
              _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ALLOC ->
              _menhir_run_140 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | LBRACE ->
          let x = _v in
          let _v = _menhir_action_087 x in
          _menhir_goto_separated_nonempty_list_COMMA_beepl_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_137 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_008 () in
      _menhir_goto_beepl_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_138 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_011 () in
      _menhir_goto_beepl_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_139 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_007 () in
      _menhir_goto_beepl_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_140 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_010 () in
      _menhir_goto_beepl_effect _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_separated_nonempty_list_COMMA_beepl_effect_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState135 ->
          _menhir_run_141 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState150 ->
          _menhir_run_151 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState329 ->
          _menhir_run_331 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_141 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let x = _v in
      let _v = _menhir_action_069 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_beepl_effect__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_beepl_effect__ : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_beepl_effect__ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState143 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_151 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_beepl_effect -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_beepl_effect (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_088 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_beepl_effect_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_331 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_027 _1 in
      _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_effect_list : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_effect_list (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _menhir_s = MenhirState333 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_164 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_020 () in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_const : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let c = _v in
      let _v = _menhir_action_030 c in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState202 ->
          _menhir_run_204 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState174 ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState192 ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState205 ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState247 ->
          _menhir_run_209 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState210 ->
          _menhir_run_211 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState212 ->
          _menhir_run_213 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState214 ->
          _menhir_run_215 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState216 ->
          _menhir_run_217 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState221 ->
          _menhir_run_222 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState223 ->
          _menhir_run_224 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState225 ->
          _menhir_run_226 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState227 ->
          _menhir_run_228 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState229 ->
          _menhir_run_230 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState231 ->
          _menhir_run_232 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState233 ->
          _menhir_run_234 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState235 ->
          _menhir_run_236 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState237 ->
          _menhir_run_238 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState239 ->
          _menhir_run_240 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState241 ->
          _menhir_run_242 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState243 ->
          _menhir_run_244 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState245 ->
          _menhir_run_246 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState201 ->
          _menhir_run_249 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState250 ->
          _menhir_run_251 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState256 ->
          _menhir_run_257 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState195 ->
          _menhir_run_259 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState260 ->
          _menhir_run_261 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState262 ->
          _menhir_run_263 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState191 ->
          _menhir_run_267 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState268 ->
          _menhir_run_269 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState271 ->
          _menhir_run_272 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState274 ->
          _menhir_run_275 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState182 ->
          _menhir_run_276 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState186 ->
          _menhir_run_276 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState181 ->
          _menhir_run_278 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState299 ->
          _menhir_run_300 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState303 ->
          _menhir_run_304 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState306 ->
          _menhir_run_307 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState180 ->
          _menhir_run_312 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState177 ->
          _menhir_run_313 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState176 ->
          _menhir_run_314 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState165 ->
          _menhir_run_317 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState163 ->
          _menhir_run_318 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState333 ->
          _menhir_run_334 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_204 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_DEREF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_DEREF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_051 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_205 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState205
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let _v = _menhir_action_054 fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState205
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState205
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState205
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState205
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState205
      | _ ->
          _eRR ()
  
  and _menhir_run_165 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_TILDE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState165 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_166 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_168 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState168 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_169 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState170 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_169 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_083 x in
          _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_IDENT_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState170 ->
          _menhir_run_171 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState168 ->
          _menhir_run_172 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_171 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_084 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_IDENT_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_172 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState174 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_175 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let s = _v in
      let _v = _menhir_action_023 s in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_176 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_REF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState176 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_177 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState177 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_178 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState178 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RULONGTYPE ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RLONGTYPE ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32TYPE ->
          _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT16TYPE ->
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FUNTYPE ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_180 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MINUS (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState180 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_181 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_MATCH (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState181 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_182 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState182 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_184 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RULONGTYPE ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RLONGTYPE ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_183 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | AND | DIV | DOT | GE | GT | LE | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | SHL | SHR | XOR ->
          let _v = _menhir_action_020 () in
          _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LBRACK | RPAREN ->
          let _v = _menhir_action_112 () in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_184 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | MUL ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_022 _menhir_stack _menhir_lexbuf _menhir_lexer
          | LPAREN ->
              let _menhir_stack = MenhirCell1_STRUCT (_menhir_stack, _menhir_s) in
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              _menhir_run_168 _menhir_stack _menhir_lexbuf _menhir_lexer
          | LBRACK | RPAREN ->
              let id = _v in
              let _v = _menhir_action_151 id in
              _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_186 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState186 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_183 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ULONGTYPE ->
          _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT8TYPE ->
          _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT32TYPE ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | UINT16TYPE ->
          _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_184 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | RULONGTYPE ->
          _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT8TYPE ->
          _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT32TYPE ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RUINT16TYPE ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RPAREN ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RLONGTYPE ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT8TYPE ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT32TYPE ->
          _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RINT16TYPE ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RBOOLTYPE ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAULONG ->
          _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT8 ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT32 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAUINT16 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RALONG ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT8 ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT32 ->
          _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RAINT16 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RABOOL ->
          _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORULONGTYPE ->
          _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT8TYPE ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT32TYPE ->
          _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORUINT16TYPE ->
          _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORSTRUCT ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORLONGTYPE ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT8TYPE ->
          _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT32TYPE ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORINT16TYPE ->
          _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORBOOLTYPE ->
          _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAULONG ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT8 ->
          _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT32 ->
          _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAUINT16 ->
          _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORALONG ->
          _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT8 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT32 ->
          _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORAINT16 ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ORABOOL ->
          _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_186 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LONGTYPE ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT8TYPE ->
          _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32TYPE ->
          _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT16TYPE ->
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FUNTYPE ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BYTES ->
          _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_187 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState189 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_193 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let l = _v in
      let _v = _menhir_action_022 l in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_194 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let i = _v in
      let _v = _menhir_action_021 i in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_195 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState195 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_196 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT32 _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RBRACK ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (id, n) = (_v, _v_0) in
                  let _v = _menhir_action_061 id n in
                  _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let id = _v in
          let _v = _menhir_action_029 id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_200 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FOR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState201 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_202 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DEREF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState202 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_203 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let b = _v in
      let _v = _menhir_action_019 b in
      _menhir_goto_const _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_218 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e) = _menhir_stack in
          let id = _v in
          let _v = _menhir_action_060 e id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_209 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState247 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE | RPAREN ->
          let x = _v in
          let _v = _menhir_action_091 x in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_210 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState210 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_212 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState212 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_227 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState227 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_214 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState214 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_243 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState243 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_229 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState229 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_239 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState239 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_216 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState216 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_221 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState221 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_225 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState225 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_245 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState245 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_231 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState231 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_233 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState233 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_235 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState235 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_237 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState237 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_223 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState223 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_241 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState241 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | UNIT ->
          _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TILDE ->
          _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRUCT ->
          _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | STRING _v ->
          _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | REF ->
          _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | OSOME ->
          _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ONONE ->
          _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MINUS ->
          _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | MATCH ->
          _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LET ->
          _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | INT64 _v ->
          _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | INT32 _v ->
          _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | IF ->
          _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | FOR ->
          _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DEREF ->
          _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOL _v ->
          _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState205 ->
          _menhir_run_207 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState247 ->
          _menhir_run_248 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState192 ->
          _menhir_run_264 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState174 ->
          _menhir_run_315 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_207 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expr (_menhir_stack, _menhir_s, fn) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_053 args fn in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_248 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_expr (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_092 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_264 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let x = _v in
      let _v = _menhir_action_073 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_LBRACE -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACE (_menhir_stack, _menhir_s) = _menhir_stack in
          let xs = _v in
          let _v = _menhir_action_006 xs in
          let _menhir_stack = MenhirCell1_array_elems (_menhir_stack, _menhir_s, _v) in
          (match (_tok : MenhirBasics.token) with
          | IN ->
              let _menhir_s = MenhirState271 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_315 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_STRUCT _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_separated_nonempty_list_COMMA_IDENT_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_separated_nonempty_list_COMMA_IDENT_ (_menhir_stack, _, fields) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_STRUCT (_menhir_stack, _menhir_s) = _menhir_stack in
          let args = _v in
          let _v = _menhir_action_059 args fields id in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_211 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_040 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_213 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_042 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_215 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_033 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_217 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_035 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_222 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_037 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_224 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_036 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_226 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_034 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_228 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_041 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_230 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_043 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_232 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_045 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_234 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_047 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_236 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_046 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_238 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | NEQ | OEQ | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_048 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_240 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_044 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_242 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_038 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_244 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | MASSGN | OR | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_039 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_246 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_052 e1 e2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_249 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_s = MenhirState250 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_251 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UP ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_024 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | DOWN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_025 () in
              _menhir_goto_dir _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_dir : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_dir (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState256 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_257 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FOR, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_dir as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_dir (_menhir_stack, d) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_FOR (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_058 d e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_259 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | THEN ->
          let _menhir_s = MenhirState260 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_261 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _menhir_s = MenhirState262 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_263 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_IF, _menhir_box_prog) _menhir_cell1_expr, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e2) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e3 = _v in
          let _v = _menhir_action_057 e1 e2 e3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_267 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _menhir_s = MenhirState268 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_269 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_expr as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_expr (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_056 e1 e2 id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_272 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_array_elems as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_array_elems (_menhir_stack, _, elems) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_055 e2 elems id t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_275 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_049 e t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_276 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let _2 = _v in
          let _v = _menhir_action_028 _2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_278 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | XOR ->
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | WITH ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BAR ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let x = () in
              let _v = _menhir_action_079 x in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | ONONE | OSOME | PBYTES ->
              let _v = _menhir_action_078 () in
              _menhir_goto_option_BAR_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | SHR ->
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_option_BAR_ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_option_BAR_ (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | PBYTES ->
          _menhir_run_282 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState281
      | OSOME ->
          _menhir_run_301 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState281
      | ONONE ->
          _menhir_run_305 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState281
      | _ ->
          _eRR ()
  
  and _menhir_run_282 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PBYTES (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | COLON ->
              let _menhir_s = MenhirState284 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_301 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_OSOME (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ARROW ->
              let _menhir_s = MenhirState303 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_305 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ONONE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState306 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_300 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ _menhir_cell0_bytes_fields as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell0_bytes_fields (_menhir_stack, fields) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_PBYTES (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_018 e fields id t in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_clause : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | BAR ->
          let _menhir_stack = MenhirCell1_clause (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState310 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | PBYTES ->
              _menhir_run_282 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_301 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_305 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | AND | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let x = _v in
          let _v = _menhir_action_081 x in
          _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_separated_nonempty_list_BAR_clause_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState281 ->
          _menhir_run_308 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState310 ->
          _menhir_run_311 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_308 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MATCH, _menhir_box_prog) _menhir_cell1_expr _menhir_cell0_option_BAR_ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_option_BAR_ (_menhir_stack, optbar) = _menhir_stack in
      let MenhirCell1_expr (_menhir_stack, _, e) = _menhir_stack in
      let MenhirCell1_MATCH (_menhir_stack, _menhir_s) = _menhir_stack in
      let cs = _v in
      let _v = _menhir_action_062 cs e optbar in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_311 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_clause -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_clause (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_082 x xs in
      _menhir_goto_separated_nonempty_list_BAR_clause_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_304 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_016 e id in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_307 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_017 e in
          _menhir_goto_clause _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_312 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_MINUS as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_MINUS (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_032 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_313 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_OSOME as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BAR | COMMA | ELSE | EOF | FUNC | HASHEBPF | IN | LET | RBRACE | RPAREN | SECTION _ | STRUCT | THEN | WITH ->
          let MenhirCell1_OSOME (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_063 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_314 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_REF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_REF (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_050 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_317 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_TILDE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_TILDE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_031 e in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_318 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EOF | FUNC | HASHEBPF | LET | SECTION _ | STRUCT ->
          let MenhirCell1_typ (_menhir_stack, _, t) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_099 anns e id t in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_toplevel : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SECTION _v_0 ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState007
      | HASHEBPF ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState007
      | FUNC | LET | STRUCT ->
          let _menhir_stack = MenhirCell1_toplevel (_menhir_stack, _menhir_s, _v) in
          let _v_1 = _menhir_action_003 () in
          _menhir_run_339 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState007 _tok
      | EOF ->
          let tl = _v in
          let _v = _menhir_action_100 tl in
          _menhir_goto_toplevel_list _menhir_stack _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_334 : type  ttv_stack. (((((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__, _menhir_box_prog) _menhir_cell1_typ, _menhir_box_prog) _menhir_cell1_effect_list as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | XOR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_210 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_212 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SHL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_227 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_effect_list (_menhir_stack, _, effs) = _menhir_stack in
          let MenhirCell1_typ (_menhir_stack, _, ret) = _menhir_stack in
          let MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ (_menhir_stack, _, xs) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
          let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
          let body = _v in
          let _v = _menhir_action_097 anns body effs id ret xs in
          _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_214 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OR ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_243 _menhir_stack _menhir_lexbuf _menhir_lexer
      | OEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_229 _menhir_stack _menhir_lexbuf _menhir_lexer
      | NEQ ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_239 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MUL ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_216 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MOD ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_221 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MINUS ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_225 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MASSGN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_245 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_231 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_205 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_233 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_235 _menhir_stack _menhir_lexbuf _menhir_lexer
      | GE ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_237 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_218 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DIV ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_223 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND ->
          let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
          _menhir_run_241 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typ_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState130 ->
          _menhir_run_131 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState123 ->
          _menhir_run_132 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_131 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typ (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_096 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typ_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_132 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_077 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_typ__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_144 : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_beepl_effect__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VARARG ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_155 () in
              _menhir_goto_vararg_flag _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | NOVARARG ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_156 () in
              _menhir_goto_vararg_flag _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_vararg_flag : type  ttv_stack. ((((ttv_stack, _menhir_box_prog) _menhir_cell1_FUNTYPE, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_typ__, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_beepl_effect__, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_typ (_menhir_stack, _, ret) = _menhir_stack in
      let MenhirCell1_loption_separated_nonempty_list_COMMA_beepl_effect__ (_menhir_stack, _, xs_inlined1) = _menhir_stack in
      let MenhirCell1_loption_separated_nonempty_list_COMMA_typ__ (_menhir_stack, _, xs) = _menhir_stack in
      let MenhirCell1_FUNTYPE (_menhir_stack, _menhir_s) = _menhir_stack in
      let va = _v in
      let _v = _menhir_action_153 ret va xs xs_inlined1 in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_152 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACE ->
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_065 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_field_decl (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState157 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_013 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RBRACE ->
              let x = _v in
              let _v = _menhir_action_093 x in
              _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_field_decl_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState012 ->
          _menhir_run_153 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState157 ->
          _menhir_run_158 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_153 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_075 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ _menhir_stack _menhir_lexbuf _menhir_lexer _v
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_field_decl__ : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
      let MenhirCell1_annotations (_menhir_stack, _menhir_s, anns) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_098 anns id xs in
      _menhir_goto_toplevel _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_158 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_field_decl -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_field_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_094 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_field_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_162 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState163 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_179 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_ONONE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | AND | BAR | COMMA | DIV | DOT | ELSE | EOF | FUNC | GE | GT | HASHEBPF | IN | LE | LET | LPAREN | LT | MASSGN | MINUS | MOD | MUL | NEQ | OEQ | OR | PLUS | RBRACE | RPAREN | SECTION _ | SHL | SHR | STRUCT | THEN | WITH | XOR ->
          let MenhirCell1_ONONE (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_064 t in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_190 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LET _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | EQ ->
          let _menhir_s = MenhirState191 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACE ->
              let _menhir_stack = MenhirCell1_LBRACE (_menhir_stack, _menhir_s) in
              let _menhir_s = MenhirState192 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TILDE ->
                  _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRING _v ->
                  _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | REF ->
                  _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | OSOME ->
                  _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ONONE ->
                  _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MINUS ->
                  _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | MATCH ->
                  _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LET ->
                  _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT64 _v ->
                  _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | INT32 _v ->
                  _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | IF ->
                  _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | FOR ->
                  _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | DEREF ->
                  _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOL _v ->
                  _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RBRACE ->
                  let _v = _menhir_action_072 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_273 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _menhir_s = MenhirState274 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | LBRACK ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_285 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | RBRACK ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _v = _menhir_action_014 () in
              _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | INT32 _v_1 ->
              _menhir_run_128 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1
          | IDENT _v_2 ->
              _menhir_run_288 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState286
          | _ ->
              _eRR ())
      | EMPTYBRACKETS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v = _menhir_action_013 () in
          _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_bytes_fields : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_bytes_fields (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_s = MenhirState299 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_164 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TILDE ->
              _menhir_run_165 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_166 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRING _v ->
              _menhir_run_175 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | REF ->
              _menhir_run_176 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | OSOME ->
              _menhir_run_177 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ONONE ->
              _menhir_run_178 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MINUS ->
              _menhir_run_180 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | MATCH ->
              _menhir_run_181 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_182 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LET ->
              _menhir_run_187 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT64 _v ->
              _menhir_run_193 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | INT32 _v ->
              _menhir_run_194 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | IF ->
              _menhir_run_195 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_196 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | FOR ->
              _menhir_run_200 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DEREF ->
              _menhir_run_202 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOL _v ->
              _menhir_run_203 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_288 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState289 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_290 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | RBRACK ->
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_012 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_bytes_field (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState295 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_288 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | RBRACK ->
              let x = _v in
              let _v = _menhir_action_089 x in
              _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState286 ->
          _menhir_run_291 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState295 ->
          _menhir_run_296 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_291 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_PBYTES _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_typ -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let x = _v in
      let _v = _menhir_action_071 x in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let xs = _v in
      let _v = _menhir_action_015 xs in
      _menhir_goto_bytes_fields _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_296 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_bytes_field -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_bytes_field (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_090 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_bytes_field_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_322 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (id, t) = (_v_0, _v) in
          let _v = _menhir_action_005 id t in
          (match (_tok : MenhirBasics.token) with
          | COMMA ->
              let _menhir_stack = MenhirCell1_arg (_menhir_stack, _menhir_s, _v) in
              let _menhir_s = MenhirState337 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | UNIT ->
                  _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ULONGTYPE ->
                  _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT8TYPE ->
                  _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT32TYPE ->
                  _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | UINT16TYPE ->
                  _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | STRUCT ->
                  _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RULONGTYPE ->
                  _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT8TYPE ->
                  _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT32TYPE ->
                  _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RUINT16TYPE ->
                  _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RLONGTYPE ->
                  _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT8TYPE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT32TYPE ->
                  _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RINT16TYPE ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RBOOLTYPE ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAULONG ->
                  _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT8 ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT32 ->
                  _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAUINT16 ->
                  _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RALONG ->
                  _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT8 ->
                  _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT32 ->
                  _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RAINT16 ->
                  _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | RABOOL ->
                  _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORULONGTYPE ->
                  _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT8TYPE ->
                  _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT32TYPE ->
                  _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORUINT16TYPE ->
                  _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORSTRUCT ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORLONGTYPE ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT8TYPE ->
                  _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT32TYPE ->
                  _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORINT16TYPE ->
                  _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORBOOLTYPE ->
                  _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAULONG ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT8 ->
                  _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT32 ->
                  _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAUINT16 ->
                  _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORALONG ->
                  _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT8 ->
                  _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT32 ->
                  _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORAINT16 ->
                  _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | ORABOOL ->
                  _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LPAREN ->
                  _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LONGTYPE ->
                  _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT8TYPE ->
                  _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT32TYPE ->
                  _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | INT16TYPE ->
                  _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | FUNTYPE ->
                  _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BYTES ->
                  _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | RPAREN ->
              let x = _v in
              let _v = _menhir_action_085 x in
              _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_arg_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState321 ->
          _menhir_run_324 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState337 ->
          _menhir_run_338 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_324 : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_067 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_arg__ : type  ttv_stack. ((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_arg__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _menhir_s = MenhirState327 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | UNIT ->
              _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ULONGTYPE ->
              _menhir_run_016 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT8TYPE ->
              _menhir_run_017 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT32TYPE ->
              _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | UINT16TYPE ->
              _menhir_run_019 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | STRUCT ->
              _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RULONGTYPE ->
              _menhir_run_023 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT8TYPE ->
              _menhir_run_024 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT32TYPE ->
              _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RUINT16TYPE ->
              _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RLONGTYPE ->
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT8TYPE ->
              _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT32TYPE ->
              _menhir_run_029 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RINT16TYPE ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RBOOLTYPE ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAULONG ->
              _menhir_run_032 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT8 ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT32 ->
              _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAUINT16 ->
              _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RALONG ->
              _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT8 ->
              _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT32 ->
              _menhir_run_056 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RAINT16 ->
              _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RABOOL ->
              _menhir_run_064 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORULONGTYPE ->
              _menhir_run_068 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT8TYPE ->
              _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT32TYPE ->
              _menhir_run_070 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORUINT16TYPE ->
              _menhir_run_071 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORSTRUCT ->
              _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORLONGTYPE ->
              _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT8TYPE ->
              _menhir_run_076 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT32TYPE ->
              _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORINT16TYPE ->
              _menhir_run_078 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORBOOLTYPE ->
              _menhir_run_079 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAULONG ->
              _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT8 ->
              _menhir_run_084 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT32 ->
              _menhir_run_088 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAUINT16 ->
              _menhir_run_092 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORALONG ->
              _menhir_run_096 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT8 ->
              _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT32 ->
              _menhir_run_104 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORAINT16 ->
              _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ORABOOL ->
              _menhir_run_112 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_116 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LONGTYPE ->
              _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT8TYPE ->
              _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT32TYPE ->
              _menhir_run_120 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | INT16TYPE ->
              _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FUNTYPE ->
              _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BYTES ->
              _menhir_run_124 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | BOOLTYPE ->
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_338 : type  ttv_stack. (ttv_stack, _menhir_box_prog) _menhir_cell1_arg -> _ -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_arg (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_086 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_arg_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_328 : type  ttv_stack. (((ttv_stack, _menhir_box_prog) _menhir_cell1_annotations _menhir_cell0_IDENT, _menhir_box_prog) _menhir_cell1_loption_separated_nonempty_list_COMMA_arg__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_prog) _menhir_state -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LBRACK ->
          _menhir_run_127 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | WRITE ->
              _menhir_run_136 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState329
          | READ ->
              _menhir_run_137 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState329
          | IO ->
              _menhir_run_138 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState329
          | EMPTYBRACKETS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let _menhir_s = MenhirState329 in
              let _v = _menhir_action_026 () in
              _menhir_goto_effect_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | DIVERGENCE ->
              _menhir_run_139 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState329
          | ALLOC ->
              _menhir_run_140 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState329
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_prog =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SECTION _v ->
          _menhir_run_001 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000
      | HASHEBPF ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | FUNC | LET | STRUCT ->
          let _v = _menhir_action_003 () in
          _menhir_run_339 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState000 _tok
      | _ ->
          _eRR ()
  
end

let prog =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_prog v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
