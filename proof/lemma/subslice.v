Require Import List Lia.
Import ListNotations.
From Minirust.def Require Import encoding utils.
From Minirust.proof.lemma Require Import utils.

Lemma subslice_zero {T s} (l: list T) : subslice_with_length l 0 s = firstn s l.
Proof.
Admitted.