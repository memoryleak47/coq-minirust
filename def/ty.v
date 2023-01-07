Require Import Datatypes Coq.Init.Byte ZArith List.
Import ListNotations.

Inductive Endianness :=
 | LittleEndian
 | BigEndian.

(* in bytes *)
Definition Size := nat.
Definition Align := nat.

(* This makes the `Context` variables globally accessible. *)
Context `{ENDIANNESS_impl : Endianness}.
Definition ENDIANNESS := ENDIANNESS_impl.

(* provenance *)
Context `{P_impl : Type}.
Definition P := P_impl.

Context `{PTR_SIZE_impl : Size}.
Definition PTR_SIZE := PTR_SIZE_impl.

Axiom ptr_size_gt0 : PTR_SIZE > 0.

Context `{P_EQ_impl : P -> P -> bool}.
Definition P_EQ := P_EQ_impl.

Axiom p_eq : forall (p q: P), (P_EQ p q) = true <-> p = q.
Axiom p_eq_false : forall (p q : P), (P_EQ p q) = false <-> p <> q.

Definition Int := Z.

Inductive Signedness :=
 | Signed : Signedness
 | Unsigned : Signedness.

(* offset, length pairs *)
Definition Chunks := list (Size * Size).

Inductive Layout :=
  | mkLayout : Align -> Size -> Layout.

Inductive PtrTy : Type :=
  | Ref (* Box is equivalent to Ref as of now. *)
  | Raw.

Inductive Ty : Type :=
 | TBool : Ty
 | TInt : Size -> Signedness -> Ty
 | TPtr : PtrTy -> Layout -> Ty
 | TTuple : list (Size * Ty) -> Size -> Ty
 | TArray : Ty -> Int -> Ty
 | TUnion : list (Size * Ty) -> Chunks -> Size -> Ty.

(* TODO somehow get `Fields` to be used in TTuple and TUnion. *)
Definition Fields := list (Size * Ty).

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

Fixpoint ty_size (t: Ty) : Size :=
  match t with
  | TBool => 1
  | TInt s _ => s
  | TPtr _ _ => PTR_SIZE
  | TTuple _ s => s
  | TArray elem count =>
    let count := Z.to_nat count in (* TODO should I consider negative count here? *)
    (ty_size elem) * count
  | TUnion _ _ s => s
  end.
