Require Import defs encoding thm lemma wf int_encoding high.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Lemma wf_int {size: Size} {signedness: Signedness} (Hwf: wf (TInt size signedness)) :
  size > 0.
Admitted.

Lemma unwrap_wrap l : forall p, unwrap_abstract (wrap_abstract l p) = Some l.
Proof.
intros p.
induction l as [|b l IH].
- reflexivity.
- simpl. rewrite IH. simpl. reflexivity.
Qed.

Inductive ValidInt : Size -> Signedness -> Value -> Type :=
  | mkValidInt {size: Size} {signedness: Signedness} {i: Int} (HR: (int_in_range i size signedness) = true) : ValidInt size signedness (VInt i).

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
simpl. unfold encode_int.
destruct (encode_int_yes HR) as [l [Henc Hl]].
simpl.
rewrite <- Henc.
exists (wrap_abstract l None).
simpl.
split. { reflexivity. }
unfold decode_int.
rewrite unwrap_wrap.
simpl.
destruct (rt1_int size signedness i HR Hs) as [l' [Hl' Hdec]].
assert (l = l') as HL. { rewrite <- Henc in Hl'. inversion Hl'. reflexivity. }
rewrite <- HL in Hdec. clear l' HL Hl'.
rewrite Hdec.
reflexivity.
Qed.

Lemma int_rt2 (size: Size) (signedness: Signedness) : rt2 (TInt size signedness).
Proof.
Admitted.