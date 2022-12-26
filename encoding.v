Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import defs.
Require Import int_encoding.

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

(* int encoding is defined in int_encoding.v *)

(* ptr *)
Definition encode_ptr (v: Value) : option (list AbstractByte) :=
  match v with
  | VPtr addr opt_p =>
    let insert_provenance := fun x =>
      match x with
      | Init b _ => Init b opt_p
      | Uninit => Uninit
      end
    in

    match encode_int PTR_SIZE Unsigned (VInt addr) with
    | Some bytes =>
      let bytes := map insert_provenance bytes in
      Some bytes
    | None => None
    end
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

  let prov :=
    match (forallb has_start_prov l) with
    | true => start_prov
    | false => None
    end
  in

  let align :=
    match ptr_ty with
    | Ref align _ _ => align
    | Box align _ => align
    | Raw align _ => align
    end
  in

  let align := Z.of_nat align in

  match decode_int PTR_SIZE Unsigned l with
  | Some (VInt addr) =>
    let constraints := (addr >? 0)%Z && (addr mod align =? 0)%Z in
    let ptr := VPtr addr prov in
    match (ptr_ty, constraints) with
    | (Raw _ _, _) => Some ptr (* raw ptrs don't need to satisfy the constraints *)
    | (_, true) => Some ptr
    | (_, false) => None
    end
  | _ => None
  end.

(* arrays *)

Definition Encoder := Ty -> Value -> option (list AbstractByte).
Definition Decoder := Ty -> list AbstractByte -> option Value.

Fixpoint transpose {T: Type} (l: list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | None::_ => None
  | (Some a)::rest =>
    let f := fun r => a::r in
    option_map f (transpose rest)
  end.

Definition encode_array (elem : Ty) (count: Int) (v: Value) (subencode: Encoder) : option (list AbstractByte) :=
  let elem_size := ty_size elem in
  let enc := fun x =>
    let opt_bytes := subencode elem x in
    match opt_bytes with
    | Some bytes =>
      match (length bytes =? elem_size) with
      | true => Some bytes
      | false => None
      end
    | None => None
    end
  in

  match v with
  | VTuple vals =>
    match (Z.of_nat (length vals) =? count)%Z with
    | true =>
      let opt_bytes := map enc vals in
      match transpose opt_bytes with
      | Some bytes => Some (concat bytes)
      | None => None
      end
    | false => None
    end
  | _ => None
 end.

Fixpoint subslice_with_length {T: Type} (l: list T) (start: nat) (length: nat) : list T :=
  match (l,start,length) with
  | (_::l', S start', ln) => subslice_with_length l' start' ln
  | (x::l', 0, S ln') => x::(subslice_with_length l' 0 ln')
  | (_, 0, 0) => []
  | ([],_,_) => []
  end.

Fixpoint write_subslice_at_index {T: Type} (l: list T) (start: nat) (other: list T) : list T :=
  match (l,start,other) with
  | (x::l', S start', o) => x::(write_subslice_at_index l' start' o)
  | (_::l', 0, y::o') => y::(write_subslice_at_index l' 0 o')
  | (l, 0, []) => l
  | ([],_,_) => []
  end.

Fixpoint chunks_impl {T: Type} (tmp: list T) (chunk_size: nat) (l: list T) : list (list T) :=
  match (chunk_size =? length tmp,l) with
  | (_,[]) => [tmp]
  | (true,x::l') => tmp::(chunks_impl [x] chunk_size l')
  | (false,x::l') => chunks_impl (tmp ++ [x]) chunk_size l'
  end.

Definition chunks {T: Type} (l: list T) (chunk_size: nat) := chunks_impl [] chunk_size l.

Definition decode_array (elem: Ty) (count: Int) (l: list AbstractByte) (subdecoder: Decoder) : option Value :=
  let elem_size := ty_size elem in
  let c := chunks l elem_size in
  let dec := subdecoder elem in
  let opt := transpose (map dec c) in
  option_map VTuple opt.

(* combining encode, decode together: *)

(* encoding can fail, if ty and val are not compatible. *)
Definition encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match ty with
  | TInt size signedness => encode_int size signedness val
  | TBool => encode_bool val
  | _ => None
 end.

Definition decode (ty : Ty) (l : list AbstractByte) : option Value :=
 match ty with
  | TInt size signedness => decode_int size signedness l
  | TBool => decode_bool l
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
