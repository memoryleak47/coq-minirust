Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Section ptr.

Context (layout: Layout).
Context (ptr_ty: PtrTy).

Definition t := TPtr ptr_ty layout.

Inductive Constraints : Int -> Type :=
  | CRaw {addr} : Constraints addr.
 (* TODO add other Constraints option *)

Inductive ValidPtr : Value -> Type :=
  | mkValidPtr addr p : Constraints addr -> ValidPtr (VPtr addr p).

Lemma valid_ptr (v: Value) (H: is_valid_for t v) :
  ValidPtr v.
Admitted.

Lemma ptr_mono1 : mono1 t.
Proof.
Admitted.

Lemma ptr_mono2 : mono2 t.
Proof.
Admitted.

Lemma ptr_rt1 : rt1 t.
Proof.
intros _ v Hval.
Admitted.

Lemma ptr_rt2 : rt2 t.
Proof.
Admitted.

End ptr.