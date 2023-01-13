From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils subslice.
Require Import List Nat PeanoNat.

Section union.

Context {params: Params}.
Context {fields: Fields}.
Context {chunks: Chunks}.
Context {size: Size}.
Notation t := (TUnion fields chunks size).
Context (Hwf: wf t).

Lemma chunks_fit_size_l : chunks_fit_size chunks size.
apply Hwf.
Qed.

Lemma chunk_size_lemma {l} (Hlen: length l = size) :
  forallb check_chunk_size (combine chunks (map (decode_union_chunk l) chunks)) = true.
Proof.
apply forallb_forall.
apply Forall_forall.
have Hfit chunks_fit_size_l.
unfold chunks_fit_size in Hfit.
clear Hwf.

induction chunks as [|c chunks' IH].
{ apply Forall_nil. }

simpl (map _ _).
simpl (combine _ _).
apply Forall_cons; cycle 1.
{ apply IH. inversion Hfit. auto. }

clear IH.
unfold check_chunk_size.
unfold decode_union_chunk.
destruct c as [offset len].
inversion Hfit.
simpl in H1.
apply Nat.eqb_eq.
rewrite subslice_length. { auto. }
rewrite Hlen.
auto.
Qed.

Lemma union_dec [l v] (H: decode t l = Some v) :
  length l = size /\
  exists data, v = VUnion data /\
  data = map (decode_union_chunk l) chunks /\
  forallb check_chunk_size (combine chunks data) = true /\
  encode t v = Some (fold_right encode_union_chunk
       (mk_uninit size) (combine chunks data)).
Proof.
unfold decode,decode_union in H.
assert (length l = size) as Hlen.
{ destruct (Nat.eqb_spec (length l) size); auto. simpl in H. discriminate H. }
split. { auto. }

rewrite Hlen in H.
rewrite Nat.eqb_refl in H.
simpl in H.
inversion H. clear H v H1.
unfold encode,encode_union.
simpl.
unfold assuming.
rewrite (map_length (decode_union_chunk l) chunks).
rewrite Nat.eqb_refl.
simpl.
rewrite (chunk_size_lemma Hlen).
eexists _.
split. { auto. }
split. { auto. }
simpl.
auto.
split. { apply (chunk_size_lemma Hlen). }
auto.
Qed.

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
