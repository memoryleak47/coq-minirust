Require Import Lia List.
Import ListNotations.
From Minirust.def Require Import ty encoding le.
From Minirust.proof.lemma Require Import le.

Section wrap_abstract.

Context {params: Params}.

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

Lemma wrap_len bl {o} : length (wrap_abstract bl o) = length bl.
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

End wrap_abstract.