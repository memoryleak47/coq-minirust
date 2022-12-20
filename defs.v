Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

(* provenance *)
Context `{P : Type}.

(* in bytes *)
Definition Size := nat.

Definition Int := Z.

Inductive Signedness :=
 | Signed : Signedness
 | Unsigned : Signedness.

Inductive Ty : Type :=
 | BoolTy : Ty
 | IntTy : Size -> Signedness -> Ty.

Inductive Value : Type :=
 | BoolVal : bool -> Value
 | IntVal : Int -> Value.

Inductive AbstractByte : Type :=
 | Uninit : AbstractByte
 | Init : byte -> option P -> AbstractByte.

(* TODO add ints! *)
Definition encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match (ty, val) with
  | (BoolTy, BoolVal true) => Some [Init x01 None]
  | (BoolTy, BoolVal false) => Some [Init x00 None]
  | _ => None
 end.

(* TODO add ints! *)
Definition decode (ty : Ty) (bytes : list AbstractByte) : option Value :=
 match (ty, bytes) with
  | (BoolTy, [Init x01 _]) => Some (BoolVal true)
  | (BoolTy, [Init x00 _]) => Some (BoolVal false)
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.