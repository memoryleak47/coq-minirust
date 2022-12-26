Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import defs.
Require Import int_encoding.
Require Import utils.

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

(* int *)
Definition encode_int (size: Size) (signedness: Signedness) (v: Value) : option (list AbstractByte) :=
  match v with
  | VInt x =>
    encode_int_raw size signedness x
    o-> (fun y => wrap_abstract y None)
  | _ => None
  end.

Definition decode_int (size: Size) (signedness: Signedness) (l: list AbstractByte) : option Value :=
  unwrap_abstract l
  >>= (fun x => decode_int_raw size signedness x)
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
Definition encode_ptr (_ptr_ty: PtrTy) (v: Value) : option (list AbstractByte) :=
  match v with
  | VPtr addr opt_p =>
    encode_int_raw PTR_SIZE Unsigned addr
    o-> (fun bytes => wrap_abstract bytes opt_p)
  | _ => None
  end.

Definition decode_ptr (ptr_ty: PtrTy) (l: list AbstractByte) : option Value :=
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

  let prov := start_prov
    >>= assuming_const (forallb has_start_prov l)
  in

  let align :=
    match ptr_ty with
    | Ref align _ _ => align
    | Box align _ => align
    | Raw align _ => align
    end
  in

  let align := Z.of_nat align in

  unwrap_abstract l
  >>= (fun bytes => decode_int_raw PTR_SIZE Unsigned bytes)
  >>= assuming (fun addr =>
    let constraints : bool := (addr >? 0)%Z && (addr mod align =? 0)%Z in
    let is_raw : bool :=
      match ptr_ty with
      | Raw _ _ => true
      | _ => false
      end
    in

    is_raw || constraints
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

Definition mk_uninit (size: Size) := map (fun _ => Uninit) (seq 0 size).

Definition decode_array (elem: Ty) (count: Int) (l: list AbstractByte) (subdecoder: Decoder) : option Value :=
  let elem_size := ty_size elem in
  let c := chunks l elem_size in
  let dec := subdecoder elem in
  let opt := transpose (map dec c) in
  opt o-> VTuple.

(* tuples *)
Definition encode_tuple (fields: Fields) (size: Size) (v: Value) (subencode: Encoder) : option (list AbstractByte) :=
  let f := fix f (l: list AbstractByte) (fields: Fields) (vals: list Value) : option (list AbstractByte) :=
    match (fields,vals) with
    | ((offset, sub_ty)::fields', v::vals') =>
      match subencode sub_ty v with
      | Some bytes =>
        let l' := write_subslice_at_index l offset bytes in
        f l' fields' vals'
      | None => None
      end
    | (_::_,[]) => None
    | ([],_::_) => None
    | ([],[]) => Some l
    end
  in

  let uninit := mk_uninit size in

  match v with
  | VTuple vals => f uninit fields vals
  | _ => None
  end.

Definition decode_tuple (fields: Fields) (size: Size) (l: list AbstractByte) (subdecode: Decoder) : option Value :=
  let f := fun arg =>
    match arg with
    | (offset, sub_ty) =>
      let sub_l := subslice_with_length l offset (ty_size sub_ty) in
      subdecode sub_ty sub_l
    end
  in

  transpose (map f fields)
  o-> VTuple
  >>= assuming_const (length l =? size).

(* unions *)
Definition encode_union (fields: Fields) (chunks: Chunks) (size: Size) (v: Value) : option (list AbstractByte) :=
  let f := fix f (l: list AbstractByte) (chunks: Chunks) (chunks_data: list (list AbstractByte)) :=
    match (chunks, chunks_data) with
    | ((offset, chunk_s)::chunks', y::chunks_data') =>
      let l' := write_subslice_at_index l offset y in
      (f l' chunks' chunks_data')
      >>= assuming_const (chunk_s =? length y)
    | (_::_,[]) => None
    | ([],_::_) => None
    | ([],[]) => Some l
    end
  in

  let uninit := mk_uninit size in

  match v with
  | VUnion chunks_data => Some chunks_data
  | _ => None
  end
  >>= assuming (fun chunks_data =>
    (length chunks_data =? length chunks)
  )
  >>= (fun chunks_data => f uninit chunks chunks_data).

Definition decode_union (fields: Fields) (chunks: Chunks) (size: Size) (l: list AbstractByte) : option Value :=
  let f := fix f (chunk_data: list (list AbstractByte)) (chunks: Chunks) :=
    match chunks with
    | (offset, chunk_s)::chunks' =>
      let bytes := subslice_with_length l offset chunk_s in
      f (chunk_data ++ [bytes]) chunks'
    | [] => VUnion chunk_data
    end
  in

  Some (f [] chunks)
  >>= assuming_const (length l =? size).

(* combining encode, decode together: *)

(* encoding can fail, if ty and val are not compatible. *)
Fixpoint encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match ty with
  | TInt size signedness => encode_int size signedness val
  | TBool => encode_bool val
  | TPtr ptr_ty => encode_ptr ptr_ty val
  | TTuple fields size => encode_tuple fields size val encode
  | TArray elem count => encode_array elem count val encode
  | TUnion fields chunks size => encode_union fields chunks size val
 end.

Fixpoint decode (ty : Ty) (l : list AbstractByte) : option Value :=
 match ty with
  | TInt size signedness => decode_int size signedness l
  | TBool => decode_bool l
  | TPtr ptr_ty => decode_ptr ptr_ty l
  | TTuple fields size => decode_tuple fields size l decode
  | TArray elem count => decode_array elem count l decode
  | TUnion fields chunks size => decode_union fields chunks size l
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
