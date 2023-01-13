From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
Require Import List Nat.

Section union.

Context {params: Params}.
Context {fields: Fields}.
Context {chunks: Chunks}.
Context {size: Size}.
Notation t := (TUnion fields chunks size).
Context (Hwf: wf t).

Lemma union_dec [l v] (H: decode t l = Some v) : exists l', encode t v = Some l'.
Proof.
unfold decode,decode_union in H.
destruct (length l =? size) eqn:Hlen; cycle 1.
{ simpl in H. discriminate H. }

simpl in H.
inversion H. clear H v H1.
unfold encode,encode_union.
simpl.
unfold assuming.
rewrite (map_length (decode_union_chunk l) chunks).
rewrite PeanoNat.Nat.eqb_refl.
simpl.
Admitted.

Lemma union_rt1 : rt1 t.
Admitted.

Lemma union_rt2 : rt2 t.
Admitted.

Lemma union_mono1 : mono1 t.
Admitted.

Lemma union_mono2 : mono2 t.
Admitted.

Lemma union_encode_len : encode_len t.
Admitted.

Lemma union_props : Props t.
Proof.
split.
- auto.
- apply union_rt1.
- apply union_rt2.
- apply union_mono1.
- apply union_mono2.
- apply union_encode_len.
Qed.

End union.
