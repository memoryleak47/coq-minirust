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

Lemma elem_ty_wf (Hwf: wf t): wf elem_ty.
Proof. inversion Hwf. inversion H0. auto. Qed.

Lemma non_neg_count (Hwf: wf t) : (count >= 0)%Z.
Proof. inversion Hwf. inversion H0. auto. Qed.

Lemma encode_elem_len {v l} (H: encode elem_ty v = Some l) : length l = ty_size elem_ty.
Proof.
Admitted.

Lemma encode_tr {vs ll}
  (H: transpose (map (encode elem_ty) vs) = Some ll) :
  transpose (map (fun x : Value => encode elem_ty x >>= decode elem_ty) vs) = Some vs.
Proof.
Admitted.

Lemma canon_transpose_len {cl ll}
  (Hwf: wf t)
  (A: transpose (map (canonicalize elem_ty) cl) = Some ll) :
  Forall (fun x => length x = ty_size elem_ty) ll.
Proof.
apply (transpose_map_Forall A).
intros x y Hcan.
apply (canonicalize_len elem_ty elem_props (elem_ty_wf Hwf) Hcan).
Qed.

Lemma encode_elim_len_check :
  (fun x => encode elem_ty x >>=
  (fun t : list AbstractByte =>
    if length t =? ty_size elem_ty
    then Some t
    else None)) = encode elem_ty.
Proof.
  apply functional_extensionality_dep.
  intros x.
  destruct (encode elem_ty x) eqn:Hx; cycle 1.
  { simpl. auto. }

  simpl.
  rewrite (encode_elem_len Hx).
  rewrite Nat.eqb_refl.
  auto.
Qed.

(* this already proves that the resulting value `v` can be encoded again *)
Lemma array_dec {l v} (Hwf: wf t) (Hdec: decode t l = Some v) :
exists vs, v = VTuple vs
/\ (Z.of_nat (length l) = Z.of_nat (ty_size elem_ty) * count)%Z
/\ transpose (map (decode elem_ty) (chunks l (ty_size elem_ty))) = Some vs
/\ (Z.of_nat (length vs) = count)%Z
/\ exists ll, transpose (map (encode elem_ty) vs) = Some ll
/\ Z.of_nat (length ll) = count%Z
/\ exists _: (Forall (fun x => length x = ty_size elem_ty) ll), encode t v = Some (concat ll).
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

(* from here on we prove `exists l', encode t v = Some l'` and related properties *)
unfold encode. fold encode.
unfold encode_array.
simpl.

unfold assuming.
assert (count >= 0)%Z as Hnnc. { apply (non_neg_count Hwf). }
destruct ((Z.of_nat (length tr_v) =? count)%Z) eqn:Hl; cycle 1. {
  assert (Z.of_nat (length tr_v) = count)%Z; cycle 1. { lia. }
  assert (length l = ty_size elem_ty * Z.to_nat count). { lia. }
  destruct (chunks_len H) as [Hcl _].
  declare m Hm (map (decode elem_ty) (chunks l (ty_size elem_ty))).
  rewrite Hm in Htr.
  assert (length m = Z.to_nat count).
  { rewrite <- Hm. rewrite map_length. auto. }
  rewrite <- (transpose_len Htr).
  lia.
}
split. { lia. }

simpl.

rewrite encode_elim_len_check.

rewrite (transpose_map Htr).
replace (fun x => decode elem_ty x >>= encode elem_ty) with (canonicalize elem_ty); cycle 1.
{ unfold canonicalize. auto. }

destruct (canonicalize_lemma2 elem_ty elem_props (elem_ty_wf Hwf) Htr) as [ll Hll].
rewrite Hll.
simpl.
exists ll.
split. { auto. }
assert (length l = ty_size elem_ty * Z.to_nat count).
{ lia. }

destruct (chunks_len H) as [Hll1 Hll2].
split. {
  rewrite <- (transpose_len Hll).
  rewrite map_length.
  rewrite Hll1.
  lia.
}

exists (canon_transpose_len Hwf Hll).
auto.
Qed.

Lemma array_rt1 : rt1 t.
Proof.
intros Hwf v Hval.
destruct Hval as [l Hdec].
destruct (array_dec Hwf Hdec) as (vs & -> & Hlen_l & Htr_dec & Hlen_vs & ll & Htr_enc & Hlen_ll & Hlen_inner_ll & Henc).
exists (concat ll).
split. { assumption. }

unfold decode. fold decode.
unfold decode_array.
rewrite (chunks_concat Hlen_inner_ll).
rewrite (transpose_map Htr_enc).
rewrite (encode_tr Htr_enc).
simpl.
assert (length ll = Z.to_nat count). { lia. }
rewrite (concat_len H Hlen_inner_ll).
assert (Z.of_nat (ty_size elem_ty * Z.to_nat count) =
    Z.of_nat (ty_size elem_ty) * count)%Z. { lia. }
rewrite H0.
rewrite Z.eqb_refl.
simpl.
auto.
Qed.

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

Lemma array_encode_len : encode_len t.
Proof.
Admitted.

Lemma array_props : Props t.
Proof.
split.
- apply array_rt1.
- apply array_rt2.
- apply array_mono1.
- apply array_mono2.
- apply array_encode_len.
Qed.

End array.
