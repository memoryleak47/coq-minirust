Require Import Lia Coq.Init.Byte FunctionalExtensionality NArith ZArith List Ndigits NArith ssrbool.
Import ListNotations.

From Minirust.def Require Import defs encoding thm utils wf.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import le utils.

Section array.

Context {elem_ty: Ty}.
Context {count: Int}.

Context (elem_props : Props elem_ty).

Notation t := (TArray elem_ty count).

(* this already proves that the resulting value `v` can be encoded again *)
Lemma array_dec {l v} (Hdec: decode t l = Some v) :
exists vs, v = VTuple vs
/\ (Z.of_nat (length l) = Z.of_nat (ty_size elem_ty) * count)%Z
/\ transpose (map (decode elem_ty) (chunks l (ty_size elem_ty))) = Some vs
/\ isSome (encode t v). (* TODO add all relevant things about this encode result *)
Proof.
unfold decode in Hdec. fold decode in Hdec.
unfold decode_array in Hdec.
match goal with
| _ : ((?tr_ >>= assuming_const ?a_) o-> VTuple) = Some v |- _ => declare tr Htr tr_; declare a Ha a_
end.
rewrite Htr,Ha in Hdec.
destruct tr as [tr_v|] eqn:Htr_v; cycle 1.
{ simpl in Hdec. discriminate Hdec. }

simpl in Hdec.
destruct a eqn:Ha_v; cycle 1.
{ simpl in Hdec. discriminate Hdec. }

simpl in Hdec.
inversion Hdec as [Hv].
exists tr_v.
split. { auto. }
split. { lia. }
split. { assumption. }
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
destruct (array_dec Hdec) as [vs [-> [Hcnt [Hvs _]]]].

assert (Z.of_nat (length vs) = count)%Z as Hvsc. {
  (* we know the length of l using Hcnt,
     and hence we know the length of vs using Hvs. *)
  admit.
}

declare e He (encode t (VTuple vs)).
(* He' is a copy of He, useful later as He will be destructed to pieces *)
have He' He.
unfold encode in He. fold encode in He.
unfold encode_array in He. simpl in He.
rewrite <- Hvsc in He. simpl in He.
unfold assuming in He.
rewrite Z.eqb_refl in He. simpl in He.
rewrite (transpose_map Hvs) in He.
Admitted.

Lemma array_rt2 : rt2 t.
intros Hwf l v Hdec.
Proof.
Admitted.

Lemma array_mono1 : mono1 t.
Proof.
Admitted.

Lemma array_mono2 : mono2 t.
Proof.
Admitted.

Lemma array_props : Props t.
Proof.
split.
- apply array_rt1.
- apply array_rt2.
- apply array_mono1.
- apply array_mono2.
Qed.

End array.
