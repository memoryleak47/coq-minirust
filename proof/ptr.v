Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Inductive Constraints : PtrTy -> Layout -> Int -> Type :=
  | CRaw {align} {size: Size} {size} {addr} : Constraints Raw (mkLayout align size) addr.
 (* TODO add other Constraints option *)

Inductive ValidPtr : PtrTy -> Layout -> Value -> Type :=
  | mkValidPtr ptr_ty layout addr p : Constraints ptr_ty layout addr -> ValidPtr ptr_ty layout (VPtr addr p).

Lemma valid_ptr (ptr_ty: PtrTy) {layout: Layout} (v: Value) (H: is_valid_for (TPtr ptr_ty layout) v) :
  ValidPtr ptr_ty layout v.
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

Lemma int_rt2 (ptr_ty: PtrTy) {layout: Layout} : rt2 (TPtr ptr_ty layout).
Proof.
Admitted.