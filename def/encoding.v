Require Import Bool Datatypes Coq.Init.Byte ZArith List.
Import ListNotations.

From Minirust.def Require Import ty int_encoding utils.

Section encoding.

Context {memory: Memory}.

Definition Encoder := Ty -> Value -> option (list AbstractByte).
Definition Decoder := Ty -> list AbstractByte -> option Value.

Fixpoint wrap_abstract (l: list byte) (p: option P) : list AbstractByte :=
  match l with
  | x::l' => (Init x p)::(wrap_abstract l' p)
  | [] => []
  end.

Fixpoint unwrap_abstract (l: list AbstractByte) : option (list byte) :=
  match l with
  | Uninit::_ => None
  | (Init x _)::l' => (unwrap_abstract l') o-> (fun y => x::y)
  | [] => Some []
  end.

Definition unique_prov (l: list AbstractByte) : option P :=
  let start_prov :=
    match l with
    | [] => None
    | Uninit::_ => None
    | (Init _ p)::_ => p
    end
  in

  let p_opt_eq := fun x y =>
    match (x, y) with
    | (Some a, Some b) => P_EQ a b
    | (None, None) => true
    | _ => false
    end
  in

  let has_start_prov := fun x =>
    match x with
    | Uninit => false
    | Init _ p => p_opt_eq p start_prov
    end
  in

  start_prov
  >>= assuming_const (forallb has_start_prov l).

(* int *)
Definition encode_int (size: Size) (signedness: Signedness) (v: Value) : option (list AbstractByte) :=
  match v with
  | VInt x => Some x
  | _ => None
  end
  >>= encode_int_raw size signedness
  o-> (fun y => wrap_abstract y None).

Definition decode_int (size: Size) (signedness: Signedness) (l: list AbstractByte) : option Value :=
  unwrap_abstract l
  >>= decode_int_raw size signedness
  o-> VInt.

(* bool *)
Definition encode_bool (v: Value) : option (list AbstractByte) :=
 match v with
  | VBool true => Some [Init x01 None]
  | VBool false => Some [Init x00 None]
  | _ => None
 end.

Definition decode_bool (l: list AbstractByte) : option Value :=
 match l with
  | [Init x01 _] => Some (VBool true)
  | [Init x00 _] => Some (VBool false)
  | _ => None
 end.

(* ptr *)
Definition encode_ptr (_ptr_ty: PtrTy) (_layout: Layout) (v: Value) : option (list AbstractByte) :=
  match v with
  | VPtr addr opt_p =>
    encode_int_raw PTR_SIZE Unsigned addr
    o-> (fun bytes => wrap_abstract bytes opt_p)
  | _ => None
  end.

Definition decode_ptr (ptr_ty: PtrTy) (layout : Layout) (l: list AbstractByte) : option Value :=
  let prov := unique_prov l in

  let align :=
    Z.of_nat (match layout with
    | mkLayout align _size => align
    end)
  in

  unwrap_abstract l
  >>= (fun bytes => decode_int_raw PTR_SIZE Unsigned bytes)
  >>= assuming (fun addr =>
    match ptr_ty with
    | Raw => true
    | Ref => (addr >? 0)%Z && (addr mod align =? 0)%Z
    end
  )
  o-> (fun addr => VPtr addr prov).

(* arrays *)

Definition encode_array (elem : Ty) (count: Int) (v: Value) (subencode: Encoder) : option (list AbstractByte) :=
  let elem_size := ty_size elem in

  let enc := fun x =>
    subencode elem x
    >>= assuming (fun bytes => length bytes =? elem_size)
  in

  match v with
  | VTuple vals => Some vals
  | _ => None
  end
  >>= assuming (fun vals =>
    (Z.of_nat (length vals) =? count)%Z
  )
  >>= (fun vals => transpose (map enc vals))
  o-> (fun bytes => concat bytes).

Definition chunks {T} (count: nat) (elem_size: nat) (l: list T) :=
  map (fun i => subslice_with_length l (i*elem_size) elem_size) (seq 0 count).

Definition decode_array (elem: Ty) (count: Int) (l: list AbstractByte) (subdecoder: Decoder) : option Value :=
  let elem_size := ty_size elem in
  let full_size := (Z.of_nat elem_size * count)%Z in
  let c := chunks (Z.to_nat count) elem_size l in
  let dec := subdecoder elem in
  transpose (map dec c)
  >>= assuming_const (Z.of_nat (length l) =? full_size)%Z
  o-> VTuple.

(* tuples *)
Definition encode_tuple_fields (l: list AbstractByte) (fields: Fields) (subencode: Encoder) (vals: list Value) :=
  (fix f l fields vals :=
    match (fields,vals) with
    | ((offset, sub_ty)::fields', v::vals') =>
      (subencode sub_ty v)
      >>= (fun bytes =>
        let l' := write_subslice_at_index l offset bytes in
        f l' fields' vals'
      )
    | _ => Some l
    end) l fields vals.

Definition encode_tuple (fields: Fields) (size: Size) (v: Value) (subencode: Encoder) : option (list AbstractByte) :=
  let uninit := repeat Uninit size in

  match v with
  | VTuple vals => Some vals
  | _ => None
  end
  >>= assuming (fun vals => length vals =? length fields)
  >>= encode_tuple_fields uninit fields subencode.

Definition decode_tuple_field (subdecode: Decoder) (l: list AbstractByte) (field: Size * Ty) :=
  let (offset, sub_ty) := field in
  let sub_l := subslice_with_length l offset (ty_size sub_ty) in
  subdecode sub_ty sub_l.

Definition decode_tuple (fields: Fields) (size: Size) (l: list AbstractByte) (subdecode: Decoder) : option Value :=
  transpose (map (decode_tuple_field subdecode l) fields)
  >>= assuming_const (length l =? size)
  o-> VTuple.

(* unions *)
Definition encode_union_chunk (l: list AbstractByte) (chunk: (Size * Size) * list AbstractByte) :=
  match chunk with
  | ((offset, _chunk_s), cdata) => write_subslice_at_index l offset cdata
  end.

Definition check_chunk_size (chunk: (Size * Size) * list AbstractByte) :=
  match chunk with
  | ((offset,chunk_s), cdata) => chunk_s =? length cdata
  end.

Definition encode_union (fields: Fields) (chunks: Chunks) (size: Size) (v: Value) : option (list AbstractByte) :=
  let uninit := repeat Uninit size in

  match v with
  | VUnion chunks_data => Some chunks_data
  | _ => None
  end
  >>= assuming (fun chunks_data =>
    (length chunks_data =? length chunks)
  )
  o-> combine chunks
  >>= assuming (forallb check_chunk_size)
  o-> (fun chunks => fold_left encode_union_chunk chunks uninit).

Definition decode_union_chunk (l: list AbstractByte) (chunk: Size * Size) :=
  match chunk with
  | (offset, chunk_s) => subslice_with_length l offset chunk_s
  end.

Definition decode_union (fields: Fields) (chunks: Chunks) (size: Size) (l: list AbstractByte) : option Value :=
  Some (map (decode_union_chunk l) chunks)
  o-> VUnion
  >>= assuming_const (length l =? size).

(* combining encode, decode together: *)

(* encoding can fail, if ty and val are not compatible. *)
Fixpoint encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match ty with
  | TInt size signedness => encode_int size signedness val
  | TBool => encode_bool val
  | TPtr ptr_ty layout => encode_ptr ptr_ty layout val
  | TTuple fields size => encode_tuple fields size val encode
  | TArray elem count => encode_array elem count val encode
  | TUnion fields chunks size => encode_union fields chunks size val
 end.

Fixpoint decode (ty : Ty) (l : list AbstractByte) : option Value :=
 match ty with
  | TInt size signedness => decode_int size signedness l
  | TBool => decode_bool l
  | TPtr ptr_ty layout => decode_ptr ptr_ty layout l
  | TTuple fields size => decode_tuple fields size l decode
  | TArray elem count => decode_array elem count l decode
  | TUnion fields chunks size => decode_union fields chunks size l
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.

End encoding.
