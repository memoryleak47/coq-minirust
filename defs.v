Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

(* provenance *)
Context `{P : Type}.

Inductive Ty : Type :=
 | BoolTy : Ty.

Inductive Value : Type :=
 | BoolVal : bool -> Value.

Inductive AbstractByte : Type :=
 | Uninit : AbstractByte
 | Init : byte -> option P -> AbstractByte.

Definition encode (ty : Ty) (val: Value) : list AbstractByte :=
 match (ty, val) with
  | (BoolTy, BoolVal true) => [Init x01 None]
  | (BoolTy, BoolVal false) => [Init x00 None]
 end.

Definition decode (ty : Ty) (bytes : list AbstractByte) : option Value :=
 match (ty, bytes) with
  | (BoolTy, [Init x01 _]) => Some (BoolVal true)
  | (BoolTy, [Init x00 _]) => Some (BoolVal false)
  | _ => None
 end.