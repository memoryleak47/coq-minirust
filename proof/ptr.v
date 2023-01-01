Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

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

Lemma ptr_mono1 : mono1 t.
Proof.
intros Hwf v1 v2 Hle Hv1 Hv2.
assert (exists a b, VPtr a b = v1). {
  destruct Hv1. unfold decode,decode_ptr in H.
  destruct (unwrap_abstract x); cycle 1. { discriminate H. }
  simpl in H.
  destruct (decode_int_raw PTR_SIZE Unsigned l); cycle 1. { discriminate H. }
  simpl in H.
  unfold utils.assuming in H. simpl in H.
  destruct (Constraints i align) eqn:E; cycle 1. { discriminate H. }
  simpl in H.
  injection H.
  intros L.
  exists i.
  eexists _.
  apply L.
}
destruct H as [addr].
destruct H as [p Hv].
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
assert (exists l, encode_int_raw PTR_SIZE Unsigned addr = Some l). {
  destruct (encode_int_raw PTR_SIZE Unsigned addr) eqn:E. { exists l. reflexivity. }
  exfalso.
  destruct Hv1 as [l Hdec].
  unfold decode,decode_ptr in Hdec.
  destruct (unwrap_abstract l) eqn:F; cycle 1.
  { simpl in Hdec. discriminate Hdec. }
  simpl in Hdec.
  destruct (decode_int_raw PTR_SIZE Unsigned l0) eqn:G; cycle 1.
  { simpl in Hdec. discriminate Hdec. }
  simpl in Hdec. unfold utils.assuming in Hdec.
  destruct (Constraints i align) eqn:H; cycle 1.
  { simpl in Hdec. discriminate Hdec. }
  simpl in Hdec.
  inversion Hdec.
  destruct (Nat.eq_dec (length l0) PTR_SIZE); cycle 1.
  -- assert (decode_int_raw PTR_SIZE Unsigned l0 = None).
     { apply (decode_int_none n). }
     rewrite G in H0. discriminate H0.
  -- destruct (rt2_int PTR_SIZE Unsigned _ e).
     { apply ptr_size_gt0. }
     inversion H0. inversion H4.
     rewrite G in H3. inversion H3.
     rewrite H1 in H8.
     rewrite H8 in H5.
     rewrite H5 in E. discriminate E.
}
destruct H as [l H].
rewrite H.
exists (wrap_abstract l p), (wrap_abstract l p').
split; try auto.
split; try auto.
clear H.
induction l as [|b l IH].
- trivial.
- simpl.
  split.
-- destruct p,p'; repeat (split || reflexivity || simpl in Hle).
--- inversion Hle. apply (proj1 (p_eq p p0)). assumption.
--- inversion Hle. assumption.
-- apply IH.
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
Admitted.

Lemma ptr_rt1 : rt1 t.
Proof.
intros _ v Hval.
Admitted.

Lemma ptr_rt2 : rt2 t.
Proof.
Admitted.

End ptr.
