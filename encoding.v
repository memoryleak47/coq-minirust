Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import defs.

(* encoding can fail, if ty and val are not compatible. *)
Definition encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match (ty, val) with
  | (TBool, VBool true) => Some [Init x01 None]
  | (TBool, VBool false) => Some [Init x00 None]
  | _ => None
 end.

Definition decode (ty : Ty) (bytes : list AbstractByte) : option Value :=
 match (ty, bytes) with
  | (TBool, [Init x01 _]) => Some (VBool true)
  | (TBool, [Init x00 _]) => Some (VBool false)
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
