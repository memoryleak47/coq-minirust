Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Context {layout: Layout}.
Context {ptr_ty: PtrTy}.
Definition t := TPtr ptr_ty layout.

Inductive Constraints : Int -> Type :=
  | CRaw {addr} : Constraints addr.
 (* TODO add other Constraints option *)

Inductive ValidPtr : Value -> Type :=
  | mkValidPtr addr p : Constraints addr -> ValidPtr (VPtr addr p).

Lemma valid_ptr (v: Value) (H: is_valid_for t v) :
  ValidPtr v.
Admitted.

Lemma ptr_mono1 (ptr_ty: PtrTy) {layout: Layout}: mono1 (TPtr ptr_ty layout).
Proof.
Admitted.

Lemma ptr_mono2 (ptr_ty: PtrTy) {layout: Layout} : mono2 (TPtr ptr_ty layout).
Proof.
Admitted.

Lemma ptr_rt1 (ptr_ty: PtrTy) {layout: Layout} : rt1 (TPtr ptr_ty layout).
Proof.
intros _ v Hval.
Admitted.

Lemma ptr_rt2 (ptr_ty: PtrTy) {layout: Layout} : rt2 (TPtr ptr_ty layout).
Proof.
Admitted.