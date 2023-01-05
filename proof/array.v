Require Import defs encoding thm lemma.
Require Import Coq.Init.Byte.
Require Import List.
Import ListNotations.

Section array.

Context (elem_ty: Ty).
Context (count: Int).

Notation t := (TArray elem_ty count).

Lemma array_mono1 : mono1 t.
Proof.
Admitted.

Lemma array_mono2 : mono2 t.
Proof.
Admitted.

Lemma array_rt1 : rt1 t.
Proof.
Admitted.

Lemma array_rt2 : rt2 t.
Proof.
Admitted.

End array.