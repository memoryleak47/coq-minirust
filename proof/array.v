Require Import Lia Coq.Init.Byte FunctionalExtensionality NArith ZArith List Ndigits NArith ssrbool.
Import ListNotations.

From Minirust.def Require Import ty encoding thm utils wf.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import le utils canonicalize chunks.

Section array.

Context {elem_ty: Ty}.
Context {count: Int}.

Context (elem_props : Props elem_ty).

Notation t := (TArray elem_ty count).

Lemma elem_ty_wf : wf elem_ty.
Proof.
Admitted.

Lemma non_neg_count : (count >= 0)%Z.
Proof.
Admitted.

Lemma encode_elem_len {v l} (H: encode elem_ty v = Some l) : length l = ty_size elem_ty.
Proof.
Admitted.

Lemma chunks_concat {T} {s} {l : list (list T)} (H: Forall (fun x => length x = s) l) :
  utils.chunks (concat l) s = l.
Proof.
Admitted.

(* this already proves that the resulting value `v` can be encoded again *)
Lemma array_dec {l v} (Hdec: decode t l = Some v) :
exists vs, v = VTuple vs
/\ (Z.of_nat (length l) = Z.of_nat (ty_size elem_ty) * count)%Z
/\ transpose (map (decode elem_ty) (chunks l (ty_size elem_ty))) = Some vs
/\ exists l', encode t v = Some l'. (* TODO add all relevant things about this encode result *)
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

unfold encode. fold encode.
unfold encode_array.
simpl.

unfold assuming.
destruct ((Z.of_nat (length tr_v) =? count)%Z) eqn:Hl; cycle 1. {
  assert (Z.of_nat (length tr_v) = count)%Z; cycle 1. { lia. }
  assert (length l = ty_size elem_ty * Z.to_nat count). { lia. }
  have Hcl (chunks_len H).
  declare m Hm (map (decode elem_ty) (chunks l (ty_size elem_ty))).
  rewrite Hm in Htr.
  assert (length m = Z.to_nat count).
  { rewrite <- Hm. rewrite map_length. auto. }
  rewrite <- (transpose_len Htr).
  rewrite H0.
  rewrite Z2Nat.id. { auto. }
  assert (count >= 0)%Z. { apply non_neg_count. }
  lia.
}

simpl.

match goal with
| |- exists l', transpose (map ?f_ tr_v) o-> _ = Some l' => declare f Hf f_
end.
rewrite Hf.

assert (Hf': f = encode elem_ty). {
  apply functional_extensionality_dep.
  intros x.
  rewrite <- Hf.
  destruct (encode elem_ty x) eqn:Hx; cycle 1.
  { simpl. auto. }

  simpl.
  rewrite (encode_elem_len Hx).
  rewrite Nat.eqb_refl.
  auto.
}
rewrite Hf'.
clear f Hf Hf'.

rewrite (transpose_map Htr).
replace (fun x => decode elem_ty x >>= encode elem_ty) with (canonicalize elem_ty); cycle 1.
{ unfold canonicalize. auto. }

destruct (canonicalize_lemma2 elem_ty elem_props elem_ty_wf Htr) as [ll Hll].
rewrite Hll.
simpl.
exists (concat ll).
auto.
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
