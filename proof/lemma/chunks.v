From Minirust.def Require Import utils.

Lemma chunks_len {T n k} {l: list T} (H: length l = n * k) : length (chunks l n) = k.
Proof.
Admitted.