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

Lemma subslice_nil {T} offset len : @subslice_with_length T [] offset len = [].
Proof.
unfold subslice_with_length.
rewrite skipn_nil.
rewrite firstn_nil.
auto.
Qed.

Lemma subslice_zero {T s} (l: list T) : subslice_with_length l 0 s = firstn s l.
Proof.
unfold subslice_with_length.
f_equal.
Qed.

Lemma subslice_cons {T x offset len} {l : list T} : subslice_with_length (x::l) (S offset) len = subslice_with_length l offset len.
Proof.
unfold subslice_with_length.
simpl.
auto.
Qed.

Lemma subslice_length {T offset len} {l: list T} (H: length l >= offset + len) :
  length (subslice_with_length l offset len) = len.
Proof.
generalize dependent offset.
generalize dependent len.
induction l as [|x l IH].
{ intros. rewrite subslice_nil. simpl in H. simpl. lia. }

intros.
destruct offset.
{ rewrite subslice_zero. rewrite firstn_length. lia. }

rewrite subslice_cons.
apply IH.
simpl in H.
lia.
Qed.

Lemma write_subslice_length {T} size offset (l l': list T)
  (Hl: size = length l)
  (Hrange: offset + length l' <= length l) :
length (write_subslice_at_index l offset l') = size.
Proof.
unfold write_subslice_at_index.
do 2 rewrite app_length.
rewrite firstn_length.
rewrite skipn_length.
lia.
Qed.

Lemma subslice_rt {T offset} {l l': list T}
  (H: length l' + offset <= length l) :
  subslice_with_length (write_subslice_at_index l offset l') offset
  (length l') = l'.
Proof.
Admitted.