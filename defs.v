Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

(* provenance *)

Inductive Endianness :=
 | LittleEndian
 | BigEndian.

(* in bytes *)
Definition Size := nat.
Definition Align := nat.

(* This makes the `Context` variables globally accessible. *)
Context `{ENDIANNESS_impl : Endianness}.
Definition ENDIANNESS := ENDIANNESS_impl.

Context `{P_impl : Type}.
Definition P := P_impl.

Context `{PTR_SIZE_impl : Size}.
Definition PTR_SIZE := PTR_SIZE_impl.

Context `{P_EQ_impl : P -> P -> bool}.
Definition P_EQ := P_EQ_impl.

Definition Int := Z.

Inductive Signedness :=
 | Signed : Signedness
 | Unsigned : Signedness.

Inductive Mutability :=
 | Mutable : Mutability
 | Immutable : Mutability.

(* offset, length pairs *)
Definition Fields := list (Size * Size).
Definition Chunks := list (Size * Size).

Inductive PtrTy : Type :=
 | Ref : Align -> Size -> Mutability -> PtrTy
 | Box : Align -> Size -> PtrTy
 | Raw : Align -> Size -> PtrTy.

Inductive Ty : Type :=
 | TBool : Ty
 | TInt : Size -> Signedness -> Ty
 | TPtr : PtrTy -> Ty
 | TTuple : Fields -> Size -> Ty
 | TArray : Ty -> Int -> Ty
 | TUnion : Fields -> Chunks -> Size -> Ty.

Inductive AbstractByte : Type :=
 | Uninit : AbstractByte
 | Init : byte -> option P -> AbstractByte.

Definition Address := Int.

Inductive Value : Type :=
 | VInt : Int -> Value
 | VBool : bool -> Value
 | VPtr : Address -> option P -> Value
 | VTuple : list Value -> Value
 | VUnion : list (list AbstractByte) -> Value.
