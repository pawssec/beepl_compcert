(* Packet descriptors are two adjacent pointer-sized fields. These operations
   model existing Bytes matching; permissions and initialization are invariants
   of the supplied packet region, not consequences of pointer shape alone. *)
Require Import ZArith Bool String List Integers AST Memory.
Import ListNotations.
Local Open Scope Z_scope.

Record packet_view : Type := {
  packet_block : Values.block;
  packet_first : ptrofs;
  packet_last : ptrofs
}.

Definition read_packet_view (m : Mem.mem) (descriptor : Values.block) (offset : ptrofs)
    : option packet_view :=
  match Mem.load Mptr m descriptor (Ptrofs.unsigned offset),
        Mem.load Mptr m descriptor (Ptrofs.unsigned offset + size_chunk Mptr) with
  | Some (Values.Vptr first_block first), Some (Values.Vptr last_block last) =>
      if (Pos.eqb first_block last_block && Z.leb (Ptrofs.unsigned first) (Ptrofs.unsigned last))%bool
      then Some {| packet_block := first_block; packet_first := first; packet_last := last |}
      else None
  | _, _ => None
  end.

Definition packet_view_valid (m : Mem.mem) (view : packet_view) : Prop :=
  Ptrofs.unsigned view.(packet_first) <= Ptrofs.unsigned view.(packet_last) /\
  Mem.valid_block m view.(packet_block) /\
  Mem.range_perm m view.(packet_block) (Ptrofs.unsigned view.(packet_first))
    (Ptrofs.unsigned view.(packet_last)) Cur Readable.

Definition packet_descriptor_valid (m : Mem.mem) (descriptor : Values.block)
    (offset : ptrofs) (view : packet_view) : Prop :=
  Mem.load Mptr m descriptor (Ptrofs.unsigned offset) =
    Some (Values.Vptr view.(packet_block) view.(packet_first)) /\
  Mem.load Mptr m descriptor (Ptrofs.unsigned offset + size_chunk Mptr) =
    Some (Values.Vptr view.(packet_block) view.(packet_last)) /\
  packet_view_valid m view.

Definition packet_header_fits (view : packet_view) (size : Z) : bool :=
  (Z.leb 0 size && Z.leb (Ptrofs.unsigned view.(packet_first) + size)
    (Ptrofs.unsigned view.(packet_last)))%bool.

Inductive packet_header_result : Type :=
| PacketHeaderFits (view : packet_view) (bytes : list Memdata.memval)
| PacketHeaderShort (view : packet_view).

Definition read_packet_header (m : Mem.mem) (descriptor : Values.block)
    (offset : ptrofs) (size : Z) : option packet_header_result :=
  match read_packet_view m descriptor offset with
  | None => None
  | Some view =>
      if packet_header_fits view size then
        match Mem.loadbytes m view.(packet_block) (Ptrofs.unsigned view.(packet_first)) size with
        | Some bytes => Some (PacketHeaderFits view bytes)
        | None => None
        end
      else Some (PacketHeaderShort view)
  end.

(* Copy into a fresh allocation so subsequent scalar loads can use the header
   layout's aligned offsets, independently of the packet's original alignment. *)
Definition copy_packet_header (m : Mem.mem) (bytes : list Memdata.memval)
    : option (Mem.mem * Values.block) :=
  let (allocated, block) := Mem.alloc m 0 (Z.of_nat (List.length bytes)) in
  match Mem.storebytes allocated block 0 bytes with
  | Some copied => Some (copied, block)
  | None => None
  end.

Definition initialized_packet_contents (bytes : list Memdata.memval) : Prop :=
  exists raw, Memdata.proj_bytes bytes = Some raw.

Require Import BeeTypes BeePL_values BeePL.

(* A wire boolean is an unsigned byte converted to bool. Loading it directly
   with Mbool would reject noncanonical but valid packet bytes such as 2. *)
Definition packet_scalar_chunk (pt : primitive_type) : memory_chunk :=
  match pt with
  | Tbool => Mint8unsigned
  | _ => transl_bchunk_cchunk (chunk_of_ptype pt)
  end.

Definition decode_packet_scalar (pt : primitive_type) (bytes : list Memdata.memval)
    : Errors.res value :=
  match pt, Memdata.decode_val (packet_scalar_chunk pt) bytes with
  | Tbool, Values.Vint i => Errors.OK (Vbool (negb (Int.eq i Int.zero)))
  | Tint _ _ _, Values.Vint i => Errors.OK (Vint i)
  | Tlong _ _, Values.Vlong i => Errors.OK (Vint64 i)
  | _, _ => Errors.Error (Errors.msg "Invalid primitive packet representation"%string)
  end.

Definition read_packet_scalar (m : Mem.mem) (block : Values.block)
    (offset : Z) (pt : primitive_type) : Errors.res value :=
  match Mem.loadbytes m block offset (size_chunk (packet_scalar_chunk pt)) with
  | Some bytes => decode_packet_scalar pt bytes
  | None => Errors.Error (Errors.msg "Packet scalar bytes are not readable"%string)
  end.

Definition normalize_packet_boolean (m : Mem.mem) (block : Values.block) (offset : Z)
    : Errors.res (Mem.mem * bool) :=
  match read_packet_scalar m block offset Tbool with
  | Errors.OK (Vbool flag) =>
      match Mem.store Mbool m block offset (Values.Val.of_bool flag) with
      | Some normalized => Errors.OK (normalized, flag)
      | None => Errors.Error (Errors.msg "Packet boolean field is not writable"%string)
      end
  | Errors.OK _ => Errors.Error (Errors.msg "Invalid packet boolean decoder result"%string)
  | Errors.Error error => Errors.Error error
  end.

Definition initialized_writable_packet_buffer (m : Mem.mem) (block : Values.block)
    (size : Z) : Prop :=
  (exists bytes, Mem.loadbytes m block 0 size = Some bytes /\
    initialized_packet_contents bytes) /\
  Mem.range_perm m block 0 size Cur Writable.

Fixpoint normalize_packet_booleans (m : Mem.mem) (block : Values.block)
    (offsets : list Z) : Errors.res Mem.mem :=
  match offsets with
  | nil => Errors.OK m
  | cons offset rest =>
      match normalize_packet_boolean m block offset with
      | Errors.OK (normalized, _) => normalize_packet_booleans normalized block rest
      | Errors.Error error => Errors.Error error
      end
  end.

(* Names are resolved against the declared layout, as in header.field access.
   Packet schemas currently contain only primitive fields. *)
Fixpoint read_packet_fields (env : Ctypes.composite_env) (members : Ctypes.members)
    (m : Mem.mem) (block : Values.block) (fields : list (ident * type))
    : Errors.res (list value) :=
  match fields with
  | nil => Errors.OK nil
  | (name, Vtype pt) :: rest =>
      match Ctypes.field_offset env name members with
      | Errors.OK (offset, Ctypes.Full) =>
          match read_packet_scalar m block offset pt with
          | Errors.OK v =>
              match read_packet_fields env members m block rest with
              | Errors.OK values => Errors.OK (v :: values)
              | Errors.Error error => Errors.Error error
              end
          | Errors.Error error => Errors.Error error
          end
      | _ => Errors.Error (Errors.msg "Packet field has no full scalar offset"%string)
      end
  | _ => Errors.Error (Errors.msg "Packet field is not primitive"%string)
  end.

Definition packet_fields_bounded (env : Ctypes.composite_env) (members : Ctypes.members)
    (size : Z) (fields : list (ident * type)) : Prop :=
  List.Forall (fun field => exists pt offset,
    snd field = Vtype pt /\
    Ctypes.field_offset env (fst field) members = Errors.OK (offset, Ctypes.Full) /\
    0 <= offset /\ offset + size_chunk (packet_scalar_chunk pt) <= size) fields.

Fixpoint packet_member_type (field : ident) (members : list bmember) : option BeeTypes.type :=
  match members with
  | BeeTypes.Member_plain name ty :: rest =>
      if ident_eq field name then Some ty else packet_member_type field rest
  | _ => None
  end.

Definition packet_member_names (members : list bmember) : list ident :=
  List.map (fun member => match member with
    | BeeTypes.Member_plain name _ => name
    | BeeTypes.Member_bitfield name _ _ _ _ _ => name
    end) members.

(* Resolve the effective source type for each name.  Repeated names therefore
   use the same first declaration as field access, rather than corrupting an
   earlier non-boolean field when a later declaration has type bool. *)
Fixpoint packet_boolean_offsets (env : Ctypes.composite_env) (members : list bmember)
    (names : list ident) : Errors.res (list Z) :=
  match names with
  | nil => Errors.OK nil
  | name :: rest =>
      match packet_member_type name members, packet_boolean_offsets env members rest with
      | Some (Vtype Tbool), Errors.OK offsets =>
          match Ctypes.field_offset env name (bmembers_cmembers members) with
          | Errors.OK (offset, Ctypes.Full) => Errors.OK (offset :: offsets)
          | _ => Errors.Error (Errors.msg "Packet boolean has no full field offset"%string)
          end
      | Some (Vtype _), Errors.OK offsets => Errors.OK offsets
      | _, Errors.Error error => Errors.Error error
      | _, _ => Errors.Error (Errors.msg "Packet schema member is not primitive"%string)
      end
  end.

Definition prepare_packet_header (env : Ctypes.composite_env) (members : list bmember)
    (m : Mem.mem) (bytes : list Memdata.memval) : Errors.res (Mem.mem * Values.block) :=
  match packet_boolean_offsets env members (packet_member_names members) with
  | Errors.OK offsets =>
      match copy_packet_header m bytes with
      | Some (copied, block) =>
          match normalize_packet_booleans copied block offsets with
          | Errors.OK normalized => Errors.OK (normalized, block)
          | Errors.Error error => Errors.Error error
          end
      | None => Errors.Error (Errors.msg "Packet header copy failed"%string)
      end
  | Errors.Error error => Errors.Error error
  end.

Definition execute_packet_match (cenv : bcomposite_env) (m : Mem.mem)
    (descriptor : Values.block) (offset : ptrofs) (sid header rest : ident)
    (fields : list (ident * type)) (yes no : expr) : Errors.res (Mem.mem * expr) :=
  match Maps.PTree.get sid cenv with
  | None => Errors.Error (Errors.msg "Unknown packet header schema"%string)
  | Some co =>
      match read_packet_header m descriptor offset co.(co_sizeof) with
      | Some (PacketHeaderShort _) =>
          Errors.OK (m, subst rest (Val (Vloc descriptor offset) Bytes) no)
      | Some (PacketHeaderFits _ bytes) =>
          match prepare_packet_header (bcomposite_composite_env cenv) co.(co_members) m bytes with
          | Errors.OK (prepared, block) =>
              match read_packet_fields (bcomposite_composite_env cenv)
                (bmembers_cmembers co.(co_members)) prepared block fields with
              | Errors.OK values =>
                  match instantiate_bytes_header header (Stype sid Ctypes.noattr) fields
                    (Vloc block Ptrofs.zero) values yes with
                  | Errors.OK body => Errors.OK (prepared, body)
                  | Errors.Error error => Errors.Error error
                  end
              | Errors.Error error => Errors.Error error
              end
          | Errors.Error error => Errors.Error error
          end
      | None => Errors.Error (Errors.msg "Invalid packet header read"%string)
      end
  end.
