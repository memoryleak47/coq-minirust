Require Import defs encoding thm lemma wf int_encoding.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Lemma wf_int {size: Size} {signedness: Signedness} (Hwf: wf (TInt size signedness)) :
  size > 0.
Admitted.

Inductive ValidInt : Size -> Signedness -> Value -> Type :=
  | mkValidInt {size: Size} {signedness: Signedness} {i: Int} : (i >= int_start size signedness)%Z -> (i < int_stop size signedness)%Z -> ValidInt size signedness (VInt i).

Lemma valid_int {size: Size} {signedness: Signedness} {v: Value} (H: is_valid_for (TInt size signedness) v) :
  ValidInt size signedness v.
Proof.
unfold is_valid_for in H.
Fail destruct H. (* why does this fail? *)
Admitted.

Lemma int_mono1 (size: Size) (signedness: Signedness) : mono1 (TInt size signedness).
Proof.
Admitted.

Lemma int_mono2 (size: Size) (signedness: Signedness) : mono2 (TInt size signedness).
Proof.
Admitted.

Lemma int_rt1 (size: Size) (signedness: Signedness) : rt1 (TInt size signedness).
Proof.
intros Hwf v Hval.
set (Hs := wf_int Hwf).
destruct (valid_int Hval).
Admitted.

Lemma int_rt2 (size: Size) (signedness: Signedness) : rt2 (TInt size signedness).
Proof.
Admitted.