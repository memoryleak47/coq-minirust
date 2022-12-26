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

Definition decode_array (elem: Ty) (count: Int) (l: list AbstractByte) (subdecoder: Decoder) : option Value :=
  let elem_size := ty_size elem in
  let c := chunks l elem_size in
  let dec := subdecoder elem in
  let opt := transpose (map dec c) in
  option_map VTuple opt.

(* combining encode, decode together: *)

(* encoding can fail, if ty and val are not compatible. *)
Fixpoint encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match ty with
  | TInt size signedness => encode_int size signedness val
  | TBool => encode_bool val
  | TArray elem count => encode_array elem count val encode
  | _ => None
 end.

Fixpoint decode (ty : Ty) (l : list AbstractByte) : option Value :=
 match ty with
  | TInt size signedness => decode_int size signedness l
  | TBool => decode_bool l
  | TArray elem count => decode_array elem count l decode
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
