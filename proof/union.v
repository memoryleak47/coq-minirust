From Minirust.def Require Import ty encoding thm wf le.
From Minirust.proof Require Import defs.

Section union.

Context {params: Params}.
Context {fields: Fields}.
Context {chunks: Chunks}.
Context {size: Size}.
Notation t := (TUnion fields chunks size).
Context (Hwf: wf t).

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
