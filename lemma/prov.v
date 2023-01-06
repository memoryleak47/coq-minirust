From Minirust.def Require Import defs encoding le.

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
