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
destruct (rt1_int size signedness i HR Hs) as [l [Henc [Hl H2]]].
exists (wrap_abstract l None).
split.
- simpl.
  rewrite <- Henc.
  simpl.
  reflexivity.
- unfold decode_int.
  rewrite unwrap_wrap.
  simpl.
  rewrite Hl.
  simpl.
  reflexivity.
Qed.

Lemma int_rt2 (size: Size) (signedness: Signedness) : rt2 (TInt size signedness).
Proof.
intros Hwf l v.
intros Hdec.
assert (is_valid_for (TInt size signedness) v) as Hval. {
 unfold is_valid_for.
 exists l. assumption.
}
destruct (valid_int Hval).
set (Hs := wf_int Hwf).
destruct (unwrap_abstract l) as [bl|] eqn:E; cycle 1. {
  exfalso.
  unfold decode,decode_int in Hdec.
  rewrite E in Hdec.
  discriminate Hdec.
}
exists (wrap_abstract bl None).
assert (length bl = size). { admit. }
destruct (rt2_int size signedness bl) as [i' [Hdec' [Henc' HR']]]; try assumption.
assert (i = i') as Hii'. { admit. }
rewrite <- Hii' in Hdec',Henc',HR'. clear Hii' i' HR'.
split.
- unfold encode,encode_int.
  simpl.
  rewrite Henc'.
  simpl.
  reflexivity.
- admit.
Admitted.