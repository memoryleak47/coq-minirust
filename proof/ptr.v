Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Section ptr.

Context (layout: Layout).

Definition align :=
  match layout with
  | mkLayout align size => align
  end.

Definition size :=
  match layout with
  | mkLayout align size => size
  end.

Context (ptr_ty: PtrTy).

Notation t := (TPtr ptr_ty layout).

Definition Constraints addr align :=
  match ptr_ty with
  | Raw => true
  | Ref => ((addr >? 0)%Z && (addr mod (Z.of_nat align) =? 0)%Z)%bool
  end = true.

Inductive ValidPtr : Value -> Type :=
  | mkValidPtr addr p : Constraints addr align -> ValidPtr (VPtr addr p).

Lemma valid_ptr (v: Value) (H: is_valid_for t v) :
  ValidPtr v.
Proof.
unfold is_valid_for in H.
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