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

Context `{P : Type}.
Context `{ENDIANNESS : Endianness}.
Context `{PTR_SIZE : Size}.

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
 | TInt : IntTy -> Ty
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