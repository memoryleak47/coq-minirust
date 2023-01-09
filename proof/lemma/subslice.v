Require Import List Lia.
Import ListNotations.
From Minirust.def Require Import encoding utils.
From Minirust.proof.lemma Require Import utils.

Lemma skipn_add {T n m} (l: list T) : skipn n (skipn m l) = skipn (n+m) l.
Proof.
generalize dependent l.
induction m as [|m IH].
{ intros l. simpl. f_equal. lia. }

intros l.
destruct l.
{ simpl. do 2 rewrite skipn_nil. auto. }

replace (n + S m) with (S (n+m)); try lia.
do 2 rewrite skipn_cons.
apply IH.
Qed.

Lemma subslice_zero {T s} (l: list T) : subslice_with_length l 0 s = firstn s l.
Proof.
unfold subslice_with_length.
f_equal.
Qed.