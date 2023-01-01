Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Inductive Constraints : PtrTy -> Int -> Type :=
  | CRaw {align} {size} {addr} : Constraints (Raw align size) addr.
 (* TODO add other Constraints option *)

Inductive ValidPtr : PtrTy -> Value -> Type :=
  | mkValidPtr ptr_ty addr p : Constraints ptr_ty addr -> ValidPtr ptr_ty (VPtr addr p).

Lemma valid_ptr (ptr_ty: PtrTy) (v: Value) (H: is_valid_for (TPtr ptr_ty) v) :
  ValidPtr ptr_ty v.
Admitted.

Lemma ptr_mono1 (ptr_ty: PtrTy) : mono1 (TPtr ptr_ty).
Proof.
Admitted.

Lemma ptr_mono2 (ptr_ty: PtrTy) : mono2 (TPtr ptr_ty).
Proof.
Admitted.

Lemma ptr_rt1 (ptr_ty: PtrTy) : rt1 (TPtr ptr_ty).
Proof.
intros _ v Hval.
Admitted.

Lemma int_rt2 (ptr_ty: PtrTy) : rt2 (TPtr ptr_ty).
Proof.
Admitted.