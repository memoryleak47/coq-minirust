Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Lemma wf_int {size: Size} {signedness: Signedness} (Hwf: wf (TInt size signedness)) :
  size > 0.
Admitted.

Lemma lemma1 bl l :
  unwrap_abstract l = Some bl ->
  le (wrap_abstract bl None) l.
Proof.
generalize dependent bl.
induction l as [|a l IH].
- intros bl A. inversion A.
  simpl.
  trivial.
- intros bl A. destruct a.
-- discriminate A.
-- simpl in A.
   destruct (unwrap_abstract l); cycle 1.
--- discriminate A.
--- simpl in A. inversion A.
    destruct bl as [|b' bl'].
---- discriminate H0.
---- inversion H0.
     rewrite <- H1. rewrite <- H1 in H0, A. clear b' H1.
     rewrite H2 in H0, IH, A. clear H2 l0 H0 A.

     assert (le (wrap_abstract bl' None) l) as IH'. { apply IH. reflexivity. }
     clear IH.
     simpl.
     split. { reflexivity. }
     apply IH'.
Qed.

Lemma lemma2 {i1: Int} {v2: Value} (H: le (VInt i1) v2) : v2 = (VInt i1).
Proof.
destruct v2; try (simpl in H; exfalso; apply H).
simpl in H. inversion H.
reflexivity.
Qed.

Inductive IntPair : Size -> Signedness -> Value -> list AbstractByte -> Prop :=
 | mkIntPair {size: Size} {signedness: Signedness} {i: Int} {l: list AbstractByte} {bl: list byte} :
  unwrap_abstract l = Some bl -> length l = size -> length bl = size -> int_in_range i size signedness = true ->
  (decode (TInt size signedness) l = Some (VInt i)) -> ((encode (TInt size signedness) (VInt i)) = Some (wrap_abstract bl None)) -> IntPair size signedness (VInt i) l.

Lemma wrap_len bl : length (wrap_abstract bl None) = length bl.
Proof.
induction bl as [|b bl IH].
- reflexivity.
- simpl. f_equal. rewrite IH. reflexivity.
Qed.

(* TODO simplify *)
Lemma unwrap_len l bl : (unwrap_abstract l = Some bl) -> length bl = length l.
Proof.
generalize dependent bl.
induction l as [|a l IH].
- intros bl A.
  simpl in A.
  inversion A.
  reflexivity.
- intros bl A.
  destruct a.
-- simpl in A. discriminate A.
-- simpl in A.
   destruct bl.
--- destruct (unwrap_abstract l).
---- simpl in A. discriminate A.
---- simpl in A. discriminate A.
--- simpl. f_equal. simpl in A. rewrite IH. { reflexivity. }
    destruct (unwrap_abstract l).
---- simpl in A. inversion A. reflexivity.
---- simpl in A. discriminate A.
Qed.

Lemma unwrap_wrap l : forall p, unwrap_abstract (wrap_abstract l p) = Some l.
Proof.
intros p.
induction l as [|b l IH].
- reflexivity.
- simpl. rewrite IH. simpl. reflexivity.
Qed.

Lemma encode_int_pair {size: Size} {signedness: Signedness} {v: Value} {l: list AbstractByte} (H: encode (TInt size signedness) v = Some l) :
  (size > 0) ->
  IntPair size signedness v l.
Proof.
intros Hs.
(* storing this equation for later, H will be manipulated *)
assert (encode (TInt size signedness) v = Some l) as Henc. { exact H. }
unfold encode,encode_int in H.
destruct v; try discriminate H.
simpl in H.
destruct (int_in_range i size signedness) eqn:HR; cycle 1. {
  rewrite (encode_int_none HR) in H. simpl in H. discriminate H.
}
destruct (rt1_int size signedness i HR Hs) as [bl [H1 [H2 H3]]].
assert (wrap_abstract bl None = l) as Hlbl. {
  rewrite <- H1 in H. simpl in H.
  inversion H.
  reflexivity.
}
rewrite <- Hlbl in H, Henc.
assert (length (wrap_abstract bl None) = size). {
  rewrite wrap_len. assumption.
}

destruct (mk_var (decode (TInt size signedness) (wrap_abstract bl None))) as [d Hd].
assert (decode (TInt size signedness) (wrap_abstract bl None) = d) as Hd'. { assumption. }
unfold decode,decode_int in Hd.
rewrite unwrap_wrap in Hd. simpl in Hd.
rewrite H2 in Hd. simpl in Hd.
rewrite <- Hd in Hd'.

assert (unwrap_abstract l = Some bl) as F. {
  rewrite <- Hlbl.
  rewrite unwrap_wrap. reflexivity.
}
rewrite Hlbl in H0,Hd'.
apply (@mkIntPair size signedness i l bl F H0 H3 HR Hd' Henc).
Qed.

Lemma decode_int_pair {size: Size} {signedness: Signedness} {v: Value} {l: list AbstractByte} (Hdec: decode (TInt size signedness) l = Some v) :
  (size > 0) ->
  IntPair size signedness v l.
Proof.
intros Hs.
set (t := TInt size signedness).
assert (decode t l = Some v) as Hdec'. { assumption. }
unfold decode,decode_int in Hdec.
destruct (unwrap_abstract l) as [bl|] eqn:Hbl; cycle 1. {
  simpl in Hdec. discriminate Hdec.
}
simpl in Hdec.
destruct (decode_int_raw size signedness bl); cycle 1. {
  simpl in Hdec. discriminate Hdec.
}
simpl in Hdec.
inversion Hdec.
rewrite <- H0 in Hdec'. clear v Hdec H0.
destruct (mk_var (unwrap_len l bl Hbl)) as [Hlen _].

assert (length bl = size). {
  unfold decode,decode_int in Hdec'. simpl in Hdec'.
  rewrite Hbl in Hdec'. simpl in Hdec'.
  destruct (PeanoNat.Nat.eq_dec (length bl) size).
-- assumption.
-- rewrite decode_int_none in Hdec'. simpl in Hdec'. discriminate Hdec'. assumption.
}
assert (length l = size). { rewrite <- H. rewrite Hlen. reflexivity. }
destruct (rt2_int size signedness bl H Hs) as [i' [H1 [H2 H3]]].
assert (i = i'). {
unfold decode,decode_int in Hdec'. simpl in Hdec'.
  rewrite Hbl in Hdec'. simpl in Hdec'. rewrite <- H1 in Hdec'. simpl in Hdec'.
  inversion Hdec'.
  reflexivity.
}
rewrite <- H4 in H1, H3, H2. clear i' H4.
apply (mkIntPair Hbl H0 H H3 Hdec'); try assumption.
unfold encode,encode_int.
simpl.
rewrite H2. simpl. f_equal.
Qed.

Lemma valid_int {size: Size} {signedness: Signedness} {v: Value} (H: is_valid_for (TInt size signedness) v) :
  (size > 0) ->
  exists (l: list AbstractByte), IntPair size signedness v l.
Proof.
intros Hs.
unfold is_valid_for in H.
destruct H.
destruct (decode_int_pair H). { apply Hs. }
exists l.
apply (mkIntPair H0 H1 H2 H3 H4 H5).
Qed.

Lemma int_mono1 (size: Size) (signedness: Signedness) : mono1 (TInt size signedness).
Proof.
intros Hwf v1 v2 Hle Hval1 Hval2.
set (Hs := wf_int Hwf).

destruct (valid_int Hval1) as [l1 P1]. apply Hs.
destruct P1.
destruct (mk_var (lemma2 Hle)) as [Hv12 _].
rewrite Hv12.
clear Hle v2 Hv12 Hval2.
exists (wrap_abstract bl None),(wrap_abstract bl None).
split; try apply H4.
split. assumption.
apply lemma1.
apply unwrap_wrap.
Qed.

Lemma int_mono2 (size: Size) (signedness: Signedness) : mono2 (TInt size signedness).
Proof.
Admitted.

Lemma int_rt1 (size: Size) (signedness: Signedness) : rt1 (TInt size signedness).
Proof.
intros Hwf v Hval.
set (Hs := wf_int Hwf).
destruct (valid_int Hval) as [l A]. { apply Hs. }
destruct A.
simpl. unfold encode_int.
destruct (rt1_int size signedness i H2 Hs) as [bl' [Henc [Hdec Hlen]]].
assert (bl = bl'). {
  unfold encode,encode_int in H4.
  simpl in H4.
  rewrite <- Henc in H4.
  simpl in H4.
  inversion H4.
  assert (unwrap_abstract (wrap_abstract bl' None) = unwrap_abstract (wrap_abstract bl None)). {
    f_equal. assumption.
  }
  do 2 rewrite unwrap_wrap in H5.
  inversion H5.
  reflexivity.
}
rewrite <- H5 in Hlen,Hdec,Henc. clear bl' H5.

exists (wrap_abstract bl None).
simpl.
split.
- simpl.
  rewrite <- Henc.
  simpl.
  reflexivity.
- unfold decode_int.
  rewrite unwrap_wrap.
  simpl.
  rewrite Hdec.
  simpl.
  reflexivity.
Qed.

Lemma int_rt2 (size: Size) (signedness: Signedness) : rt2 (TInt size signedness).
Proof.
intros Hwf l v.
set (Hs := wf_int Hwf).
intros Hdec.
destruct (decode_int_pair Hdec). { apply Hs. }

exists (wrap_abstract bl None).

destruct (rt2_int size signedness bl) as [i' [Hdec' [Henc' HR']]]; try assumption.
assert (i=i'). {
  unfold decode,decode_int in H3.
  rewrite H in H3.
  simpl in H3.
  rewrite <- Hdec' in H3.
  simpl in H3.
  inversion H3.
  reflexivity.
}
rewrite <- H5 in Hdec', Henc', HR'.
clear H5 i' HR'.

split.
- unfold encode,encode_int.
  simpl.
  rewrite Henc'.
  simpl.
  reflexivity.
- apply lemma1.
  assumption.
Qed.