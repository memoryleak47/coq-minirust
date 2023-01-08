Require Import Coq.Init.Byte List ZArith Lia.
Import ListNotations.

From Minirust.def Require Import ty encoding thm wf int_encoding le utils.
From Minirust.proof.lemma Require Import unique_prov wrap_abstract le utils.
From Minirust.proof Require Import defs high int.

Section ptr.

Context (layout: Layout).

Notation align := (
  match layout with
  | mkLayout align size => align
  end).

Notation size := (
  match layout with
  | mkLayout align size => size
  end).

Context (ptr_ty: PtrTy).

Notation t := (TPtr ptr_ty layout).

Notation Constraints addr align := (
  match ptr_ty with
  | Raw => true
  | Ref => ((addr >? 0)%Z && (addr mod (Z.of_nat align) =? 0)%Z)%bool
  end).

Lemma ptr_dec {v} {l} (Hdec: decode t l = Some v) :
exists addr, v = VPtr addr (unique_prov l) /\
exists bl, encode_int_raw PTR_SIZE Unsigned addr = Some bl
/\ decode_int_raw PTR_SIZE Unsigned bl = Some addr
/\ Constraints addr align = true /\ unwrap_abstract l = Some bl.
Proof.
unfold decode,decode_ptr in Hdec.

destruct (unwrap_abstract l) eqn:Hunw; cycle 1.
{ simpl in Hdec. discriminate Hdec. }

simpl in Hdec.
destruct (decode_int_raw PTR_SIZE Unsigned l0) eqn:Hidec; cycle 1.
{ simpl in Hdec. discriminate Hdec. }

unfold assuming in Hdec.
simpl in Hdec.
destruct (Constraints i align) eqn:Hconstr; cycle 1.
{ simpl in Hdec. discriminate Hdec. }

simpl in Hdec.
exists i.
split.
{ inversion Hdec. auto. }

exists l0.
assert (length l0 = PTR_SIZE). {
  destruct (Nat.eq_dec (length l0) PTR_SIZE). { assumption. }
  rewrite decode_int_none in Hidec; try assumption. discriminate Hidec.
}

split. {
  destruct (rt2_int PTR_SIZE Unsigned l0 H ptr_size_gt0) as (i' & B & C & D).
  assert (i = i'). {
    rewrite <- B in Hidec. inversion Hidec. auto.
  }
  rewrite <- H0 in C.
  apply C.
}

split. { assumption. }
split. { assumption. }
auto.
Qed.

Lemma ptr_mono1 : mono1 t.
Proof.
intros Hwf v1 v2 Hle Hv1 Hv2.
assert (exists a b l, VPtr a b = v1 /\ encode_int_raw PTR_SIZE Unsigned a = Some l). {
  destruct Hv1 as [la H].
  destruct (ptr_dec H) as [addr [Hv [l [Henc [Hdec HConstr]]]]].
  exists addr, (unique_prov la), l.
  auto.
}
destruct H as [addr].
destruct H as [p [l [Hv Henc]]].
rewrite <- Hv.
rewrite <- Hv in Hle,Hv1. clear v1 Hv.
assert (exists b, VPtr addr b = v2). {
  destruct v2 eqn:E; try contradiction Hle.
  simpl in Hle.
  destruct Hle.
  rewrite H.
  exists o.
  reflexivity.
}
destruct H as [p' Hrew].
rewrite <- Hrew. rewrite <- Hrew in Hle,Hv2. clear Hrew v2.
unfold encode,encode_ptr.

rewrite Henc.
exists (wrap_abstract l p), (wrap_abstract l p').
split; try auto.
split; try auto.
clear Henc.

induction l as [|b l IH].
{ simpl. trivial. }

simpl.
split.
- destruct p,p'; repeat (split || reflexivity || simpl in Hle).
-- inversion Hle. apply (proj1 (p_eq p p0)). assumption.
-- inversion Hle. assumption.
- apply IH.
Qed.

Lemma ptr_mono2 : mono2 t.
Proof.
intros Hwf l1 l2 Hle.
destruct (unwrap_abstract l1) eqn:Hunw; cycle 1. {
  unfold decode,decode_ptr. rewrite Hunw. simpl. trivial.
}
destruct (decode_int_raw PTR_SIZE Unsigned l) eqn:Hdec; cycle 1. {
  unfold decode,decode_ptr. rewrite Hunw. simpl. rewrite Hdec. simpl.
  trivial.
}
destruct (Constraints i align) eqn:Hc; cycle 1. {
  unfold decode,decode_ptr. rewrite Hunw. simpl. rewrite Hdec. simpl.
  unfold utils.assuming.
  rewrite Hc. simpl. trivial.
}

unfold decode,decode_ptr. rewrite Hunw. simpl. rewrite Hdec. simpl.
unfold utils.assuming. rewrite Hc.
simpl.

assert (unwrap_abstract l2 = Some l).
{ apply (unwrap_le_some Hle Hunw); assumption. }

rewrite H.
simpl.
rewrite Hdec.
simpl.
rewrite Hc.
simpl.
split. { auto. }

destruct (unique_prov l1) eqn:E; cycle 1. { trivial. }
rewrite (unique_le Hle p).
- apply (proj2 (p_eq p p)). auto.
- assumption.
Qed.

Lemma ptr_rt1 : rt1 t.
Proof.
intros _ v Hval.
unfold is_valid_for in Hval.
destruct (Hval) as [l Hl].
destruct (ptr_dec Hl) as [addr [Hrew [bl [Henc [Hdec [Hconstr _]]]]]].
rewrite Hrew. rewrite Hrew in Hval,Hl. clear v Hrew.

exists (wrap_abstract bl (unique_prov l)).
split.
{ simpl. rewrite Henc. simpl. auto. }

simpl.
unfold decode_ptr.
rewrite unwrap_wrap.
simpl.

rewrite Hdec.
simpl.

destruct (Nat.eq_dec (length bl) PTR_SIZE) eqn:E; cycle 1.
{ rewrite decode_int_none in Hdec; try assumption. discriminate Hdec. }

assert (length bl > 0) as H.
{ rewrite e. apply ptr_size_gt0. }

rewrite (unique_wrap H).

unfold assuming.
rewrite Hconstr.
simpl.
auto.
Qed.

Lemma ptr_rt2 : rt2 t.
Proof.
intros Hwf l v Hdec.
destruct (ptr_dec Hdec) as [addr [Hv [bl (He & Hd & [Hconstr Hl])]]].
rewrite Hv.
exists (wrap_abstract bl (unique_prov l)).
split.
{ simpl. rewrite He. simpl. auto. }

apply wrap_unique_le; assumption.
Qed.

Lemma ptr_encode_len : encode_len t.
Proof.
intros Hwf v l Henc.
unfold encode,encode_ptr in Henc.
destruct v; try discriminate Henc.
destruct (int_in_range a PTR_SIZE Unsigned) eqn:E; cycle 1.
{ rewrite (encode_int_none E) in Henc. discriminate Henc. }

destruct (rt1_int PTR_SIZE Unsigned a E ptr_size_gt0) as (bl' & Hbl' & _ & Out).
rewrite <- Hbl' in Henc.
simpl in Henc.
inversion Henc.
rewrite wrap_len.
assumption.
Qed.

Lemma ptr_props : Props t.
Proof.
split.
- apply ptr_rt1.
- apply ptr_rt2.
- apply ptr_mono1.
- apply ptr_mono2.
- apply ptr_encode_len.
Qed.

End ptr.
