Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import defs.

(* int *)
Definition encode_int (int_ty: IntTy) (v: Value) : option (list AbstractByte).
Admitted.

Definition decode_int (int_ty: IntTy) (l: list AbstractByte) : option Value.
Admitted.

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

(* combining encode, decode together: *)

(* encoding can fail, if ty and val are not compatible. *)
Definition encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match ty with
  | TInt int_ty => encode_int int_ty val
  | TBool => encode_bool val
  | _ => None
 end.

Definition decode (ty : Ty) (l : list AbstractByte) : option Value :=
 match ty with
  | TInt int_ty => decode_int int_ty l
  | TBool => decode_bool l
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
