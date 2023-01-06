From Minirust.def Require Import defs encoding le.
From Minirust.lemma Require Import le.

Lemma unwrap_le bl l :
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

Lemma unwrap_le_some {l1 l2: list AbstractByte} {lb} (Hle: le l1 l2) (Hunw: unwrap_abstract l1 = Some lb) : unwrap_abstract l2 = Some lb.
Proof.
generalize dependent lb.
induction (mk_le_list _ _ Hle) as [|ab1 ab2 l1 l2 HLe IH HLeA Hlec].
{ intros. assumption. }

intros lb Hunw.

destruct ab1 as [|b1 o1].
{ simpl in Hunw. discriminate Hunw. }

destruct ab2 as [|b2 o2].
{ simpl in Hlec. destruct o1; contradiction (proj1 Hlec). }

destruct (unwrap_abstract l1) as [lb1|] eqn:Hunw1; cycle 1.
{ simpl in Hunw. rewrite Hunw1 in Hunw. simpl in Hunw. discriminate Hunw. }

assert (le l1 l2) as Hle'.
{ simpl in Hle. inversion Hle. assumption. }

assert (unwrap_abstract l2 = Some lb1) as Hunw2.
{ apply (IH Hle' lb1). auto. }

assert (b1 = b2). {
  inversion HLeA.
  - rewrite <- H. auto.
  - reflexivity.
}

simpl. rewrite Hunw2.
simpl. f_equal.

simpl in Hunw. rewrite Hunw1 in Hunw. simpl in Hunw.
injection Hunw.
intros A.
rewrite <- H.
assumption.
Qed.

Lemma unique_prov_cons2 {a} {b} {l} {p} (H: unique_prov (a :: b :: l) = Some p) :
  unique_prov (b :: l) = Some p.
Proof.

destruct a.
{ discriminate H. }

destruct o; cycle 1.
{ discriminate H. }

destruct b.
{ unfold unique_prov in H. simpl in H. rewrite (proj2 (p_eq p0 p0)) in H. discriminate H. auto. }

destruct o; cycle 1.
{ unfold unique_prov in H. simpl in H. rewrite (proj2 (p_eq p0 p0)) in H. discriminate H. auto. }

destruct (P_EQ p0 p1) eqn:E.
- rewrite (proj1 (p_eq p0 p1)) in H; cycle 1. { assumption. }
  unfold unique_prov in H.
  simpl in H.
  rewrite (proj2 (p_eq p1 p1)) in H; cycle 1. { auto. }
  simpl in H.
  unfold unique_prov.
  simpl.
  rewrite (proj2 (p_eq p1 p1)); cycle 1. { auto. }
  simpl. assumption.
- unfold unique_prov in H.
  simpl in H.
  rewrite (proj2 (p_eq p0 p0)) in H; cycle 1. { auto. }
  assert (p0 <> p1).
  { apply p_eq_false. assumption. }
  rewrite (proj2 (p_eq_false p1 p0)) in H; cycle 1.
  { auto. }
  simpl in H.
  discriminate H.
Qed.

Lemma unique_le {l1 l2: list AbstractByte} (Hle: le l1 l2) p (H: unique_prov l1 = Some p) :
  unique_prov l2 = Some p.
Proof.
assert (l1 = l2); cycle 1.
{ rewrite <- H0. auto. }

induction (mk_le_list _ _ Hle) as [| ab1 ab2 l1 l2 HLe IH HLeAB _].
{ auto. }

assert (le l1 l2) as Hle'.
{ simpl in Hle. inversion Hle. assumption. }

assert (ab1 = ab2). {
  destruct ab1.
  { unfold unique_prov in H. simpl in H. discriminate H. }

  destruct HLeAB.
  - unfold unique_prov in H. discriminate H.
  - unfold unique_prov in H. discriminate H.
  - simpl in Hle. inversion Hle. inversion H0; auto.
}
rewrite <- H0. rewrite <- H0 in Hle,HLeAB. clear H0 ab2.
f_equal.

destruct l1.
- destruct l2.
-- auto.
-- contradiction Hle'.
- apply IH.
-- assumption.
-- apply (unique_prov_cons2 H).
Qed.
