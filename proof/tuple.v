From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils subslice le.
Require Import List Nat PeanoNat Bool Lia.
Import ListNotations.

Section tuple.

Context {params: Params}.
Context {fields: Fields}.
Context {size: Size}.

Notation t := (TTuple fields size).
Context (Hwf: wf t).

(* TODO extend *)
Lemma tuple_dec [l v] (H: decode t l = Some v) :
  length l = size /\
  exists vals, v = VTuple vals /\
  exists l', encode t v = Some l'.
Admitted.

Lemma tuple_rt1 : rt1 t.
Admitted.

Lemma tuple_rt2 : rt2 t.
Admitted.

Lemma tuple_mono1 : mono1 t.
Admitted.

Lemma tuple_mono2 : mono2 t.
Admitted.

Lemma tuple_encode_len : encode_len t.
Admitted.

Lemma tuple_props : Props t.
Proof.
split.
- auto.
- apply tuple_rt1.
- apply tuple_rt2.
- apply tuple_mono1.
- apply tuple_mono2.
- apply tuple_encode_len.
Qed.

End tuple.
