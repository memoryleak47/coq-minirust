Require Import Coq.Init.Byte FunctionalExtensionality NArith ZArith List Ndigits NArith.
Import ListNotations.

From Minirust.def Require Import defs encoding thm utils wf.
From Minirust.lemma Require Import utils le.

Section array.

Context (elem_ty: Ty).
Context (count: Int).

Notation t := (TArray elem_ty count).

Lemma array_dec {l v} (Hdec: decode t l = Some v) :
exists vs, v = VTuple vs /\ Z.of_nat (length vs) = count.
Proof.
unfold decode in Hdec. fold decode in Hdec.
unfold decode_array in Hdec.
Admitted.

Lemma encode_len {v ty l} (H: encode t v = Some l) : length l = ty_size ty.
Proof.
Admitted.

Lemma chunks_concat {T} {s} {l : list (list T)} (H: Forall (fun x => length x = s) l) :
  utils.chunks (concat l) s = l.
Proof.
Admitted.

Lemma array_rt1 : rt1 t.
Proof.
intros Hwf v Hval.
destruct Hval as [l Hdec].
destruct (array_dec Hdec) as [vs [-> Hcnt]].
Admitted.

Lemma array_rt2 : rt2 t.
Proof.
Admitted.

Lemma array_mono1 : mono1 t.
Proof.
Admitted.

Lemma array_mono2 : mono2 t.
Proof.
Admitted.

End array.
