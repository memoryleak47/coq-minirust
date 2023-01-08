Require Import List.
Import ListNotations.
From Minirust.def Require Import utils.

Lemma chunks_len {T n k} {l: list T} (H: length l = n * k) :
  length (chunks l n) = k /\ Forall (fun x => length x = n) (chunks l n).
Proof.
Admitted.

Lemma chunks_concat {T} {s} {l : list (list T)} (H: Forall (fun x => length x = s) l) :
  chunks (concat l) s = l.
Proof.
Admitted.