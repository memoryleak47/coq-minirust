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
Definition Align := nat.

Definition Int := Z.

Inductive Signedness :=
 | Signed : Signedness
 | Unsigned : Signedness.

Inductive Mutability :=
 | Mutable : Mutability
 | Immutable : Mutability.

Record Layout : Type := mkLayout {
  l_align : Align;
  l_size : Size
  (* inhabited is ommited, as currently each type is inhabited. *)
}.

(* offset, length pairs *)
Definition Fields := list (Size * Size).
Definition Chunks := list (Size * Size).

Record IntTy := mkIntTy {
  i_size: Size;
  i_signed: Signedness
}.

Inductive PtrTy : Type :=
 | Ref : Mutability -> Layout -> PtrTy
 | Box : Layout -> PtrTy
 | Raw : Layout -> PtrTy.

Inductive Ty : Type :=
 | TBool : Ty
 | TInt : Size -> Signedness -> Ty
 | TPtr : PtrTy -> Ty
 | TTuple : Fields -> Size -> Ty
 | TArray : Ty -> Int -> Ty
 | TUnion : Fields -> Chunks -> Size -> Ty.

Record Pointer := mkPointer {
  p_addr: Int;
  p_prov: option P
}.

Inductive AbstractByte : Type :=
 | Uninit : AbstractByte
 | Init : byte -> option P -> AbstractByte.

Inductive Value : Type :=
 | VInt : Int -> Value
 | VBool : bool -> Value
 | VPtr : Pointer -> Value
 | VTuple : list Value -> Value
 | VUnion : list (list AbstractByte) -> Value.

(* TODO add ints! *)
Definition encode (ty : Ty) (val: Value) : option (list AbstractByte) :=
 match (ty, val) with
  | (TBool, VBool true) => Some [Init x01 None]
  | (TBool, VBool false) => Some [Init x00 None]
  | _ => None
 end.

(* TODO add ints! *)
Definition decode (ty : Ty) (bytes : list AbstractByte) : option Value :=
 match (ty, bytes) with
  | (TBool, [Init x01 _]) => Some (VBool true)
  | (TBool, [Init x00 _]) => Some (VBool false)
  | _ => None
 end.

Definition is_valid_for (ty : Ty) (v : Value) := exists l, decode ty l = Some v.
