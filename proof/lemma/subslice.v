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
unfold subslice_with_length,write_subslice_at_index.
rewrite skipn_app.
assert ((offset - length (firstn offset l) = 0)) as ->.
{ rewrite firstn_length. lia. }
simpl.
rewrite skipn_firstn_comm.
assert (offset - offset = 0) as ->. { lia. }
simpl.
rewrite firstn_app.
assert (length l' - length l' = 0) as ->. { lia. }
simpl.
rewrite firstn_all.
rewrite app_nil_end.
auto.
Qed.

Lemma subslice_independent_write {T} {offset offset'} {d d' a: list T}
(Horig: subslice_with_length a offset (length d) = d)
(Hindep: offset + length d <= offset') :
subslice_with_length (write_subslice_at_index a offset' d') offset (length d) =
d.
Proof.
unfold subslice_with_length,write_subslice_at_index.
unfold subslice_with_length in Horig.
rewrite skipn_app.
rewrite firstn_app.
rewrite skipn_length.
rewrite firstn_length.
assert (length a - offset >=  length d). {
  assert (length (firstn (length d) (skipn offset a)) = length d). { f_equal. auto. }
  rewrite firstn_length,skipn_length in H.
  lia.
}
assert (length d - (Nat.min offset' (length a) - offset) = 0) as ->. { lia. }
simpl.
rewrite <- app_nil_end.

rewrite skipn_firstn_comm.
rewrite firstn_firstn.
assert (Nat.min (length d) (offset' - offset) = length d) as ->. { lia. }
auto.
Qed.

Lemma firstn_nth {T i def n} {l: list T}
  (H1 : n > i)
  (H2 : length l > i) :
nth i (firstn n l) def = nth i l def.
Proof.
Admitted.

Lemma skipn_nth {T i def n} {l: list T}
  (H : length l > i+n) :
nth i (skipn n l) def = nth (i+n) l def.
Proof.
Admitted.

Lemma subslice_nth {T offset len i} {l: list T} def
  (Hi: i < len)
  (H: length l >= offset + len) :
  nth i (subslice_with_length l offset len) def = nth (i+offset) l def.
Proof.
unfold subslice_with_length.
rewrite firstn_nth; try lia; cycle 1.
{ rewrite skipn_length. lia. }

rewrite skipn_nth; try lia.
auto.
Qed.