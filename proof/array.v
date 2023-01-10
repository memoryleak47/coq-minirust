Require Import Lia Coq.Init.Byte FunctionalExtensionality NArith ZArith List Ndigits NArith ssrbool.
Import ListNotations.

From Minirust.def Require Import ty encoding thm utils wf.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import le utils canonicalize chunks.

Section array.

Context [elem_ty: Ty].
Context [count: Int].

Context (props_IH : wf elem_ty -> Props elem_ty).

Notation t := (TArray elem_ty count).
Context (Hwf: wf t).

Lemma elem_ty_wf : wf elem_ty.
Proof. inversion Hwf. inversion H0. auto. Qed.

Definition elem_props := props_IH elem_ty_wf.

Lemma non_neg_count : (count >= 0)%Z.
Proof. inversion Hwf. inversion H0. auto. Qed.

Lemma encode_elem_len {v l} (H: encode elem_ty v = Some l) : length l = ty_size elem_ty.
Proof.
apply (PR_ENCODE_LEN elem_ty elem_props _ _ H).
Qed.

Lemma encode_tr {vs ll orig_ll}
  (Hdec: transpose (map (decode elem_ty) orig_ll) = Some vs)
  (H: transpose (map (encode elem_ty) vs) = Some ll) :
  transpose (map (fun x : Value => encode elem_ty x >>= decode elem_ty) vs) = Some vs.
Proof.
generalize dependent orig_ll.
generalize dependent vs.
induction ll as [|x ll IH]. {
  intros vs Henc ll Hdec.
  rewrite (transpose_nil Henc).
  simpl.
  auto.
}

intros vs Henc ll' Hdec.
destruct vs as [|v vs'].
{ simpl. auto. }

assert (is_valid_for elem_ty v). {
  destruct ll'.
  { simpl in Hdec. inversion Hdec. }

  simpl in Hdec.
  destruct (decode elem_ty l) eqn:E; cycle 1.
  { discriminate Hdec. }

  destruct (transpose (map (decode elem_ty) ll')); cycle 1.
  { simpl in Hdec. discriminate Hdec. }

  simpl in Hdec.
  inversion Hdec.
  rewrite <- H0.
  exists l.
  assumption.
}

destruct (PR_RT1 elem_ty elem_props v H) as (x' & Henc' & Hdec').
simpl.
rewrite Henc'.
simpl.
rewrite Hdec'.
simpl.
assert (transpose (map (encode elem_ty) vs') = Some ll). {
  clear - vs' ll Henc.
  simpl in Henc.
  destruct (encode elem_ty v); cycle 1.
  { simpl in Henc. discriminate Henc. }

  destruct (transpose (map (encode elem_ty) vs')); cycle 1.
  { simpl in Henc. discriminate Henc. }

  simpl in Henc. inversion Henc.
  auto.
}
destruct ll'.
{ simpl in Hdec. discriminate Hdec. }

assert (transpose (map (decode elem_ty) ll') = Some vs'). {
  clear - ll' vs' Hdec.
  simpl in Hdec.
  destruct (decode elem_ty l); cycle 1.
  { discriminate Hdec. }

  destruct (transpose (map (decode elem_ty) ll')); cycle 1.
  { simpl in Hdec. discriminate Hdec. }

  simpl in Hdec.
  inversion Hdec.
  auto.
}

rewrite (IH vs' H0 ll' H1).
simpl.
auto.
Qed.


Lemma canon_transpose_len {cl ll}
  (A: transpose (map (canonicalize elem_ty) cl) = Some ll) :
  Forall (fun x => length x = ty_size elem_ty) ll.
Proof.
apply (transpose_map_Forall A).
intros x y Hcan.
apply (canonicalize_len elem_props Hcan).
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
Lemma array_dec {l v} (Hdec: decode t l = Some v) :
exists vs, v = VTuple vs
/\ (Z.of_nat (length l) = Z.of_nat (ty_size elem_ty) * count)%Z
/\ transpose (map (decode elem_ty) (chunks (Z.to_nat count) (ty_size elem_ty) l)) = Some vs
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
assert (count >= 0)%Z as Hnnc. { apply non_neg_count. }
destruct ((Z.of_nat (length tr_v) =? count)%Z) eqn:Hl; cycle 1. {
  assert (Z.of_nat (length tr_v) = count)%Z; cycle 1. { lia. }
  assert (length l = ty_size elem_ty * Z.to_nat count). { lia. }
  destruct (chunks_len H) as [Hcl _].
  declare m Hm (map (decode elem_ty) (chunks (Z.to_nat count) (ty_size elem_ty) l)).
  rewrite Hm in Htr.
  assert (length m = Z.to_nat count).
  { rewrite <- Hm. rewrite map_length. auto. refine (proj1 (chunks_len _)). lia. }
  rewrite <- (transpose_len Htr).
  lia.
}
split. { lia. }

simpl.

rewrite encode_elim_len_check.

rewrite (transpose_map Htr).
replace (fun x => decode elem_ty x >>= encode elem_ty) with (canonicalize elem_ty); cycle 1.
{ unfold canonicalize. auto. }

destruct (canonicalize_lemma2 elem_props Htr) as [ll Hll].
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
  assert (length (chunks (Z.to_nat count) (ty_size elem_ty) l) = Z.to_nat count).
  { refine (proj1 (chunks_len _)). lia. }
  lia.
}

exists (canon_transpose_len Hll).
auto.
Qed.

Lemma array_rt1 : rt1 t.
Proof.
intros v Hval.
destruct Hval as [l Hdec].
destruct (array_dec Hdec) as (vs & -> & Hlen_l & Htr_dec & Hlen_vs & ll & Htr_enc & Hlen_ll & Hlen_inner_ll & Henc).
exists (concat ll).
split. { assumption. }

unfold decode. fold decode.
unfold decode_array.
assert (length ll = Z.to_nat count) as Hlen_ll'. { lia. }
rewrite (chunks_concat Hlen_ll' Hlen_inner_ll).
rewrite (transpose_map Htr_enc).
rewrite (encode_tr Htr_dec Htr_enc).
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
Proof.
intros l v Hdec.
destruct (array_dec Hdec) as (vs & -> & Hlen_l & Htr_dec & Hlen_vs & ll & Htr_enc & Hlen_ll & Hlen_inner_ll & Henc).
exists (concat ll).
split. { assumption. }

(* thoughts:
l will be converted with l = concat (chunks l)
And then we can prove some general `le (concat a) (concat b)`,
if a and b have the same shapes;
and if a and b are element-wise le (I can use combine to express this).

For i we then know that decode (chunks l)[i] = vs[i] and encode vs[i] = ll[i].
Hence we just have to apply rt2 of elem_ty.
*)
Admitted.

Lemma array_mono1 : mono1 t.
Proof.
Admitted.

Lemma array_mono2 : mono2 t.
Proof.
Admitted.

Lemma array_encode_len : encode_len t.
Proof.
intros v l Henc.
unfold encode in Henc. fold encode in Henc.
unfold encode_array in Henc.
destruct v; try discriminate Henc.
simpl in Henc.
unfold assuming in Henc.
destruct (Z.of_nat (length l0) =? count)%Z eqn:E; try discriminate Henc.
simpl in Henc.
match goal with
| _ : (?a_ o-> _ = Some l) |- _ => declare a Ha a_
end.
destruct a; cycle 1.
{ rewrite Ha in Henc.  discriminate Henc. }

rewrite Ha in Henc.
simpl in Henc.
inversion Henc.
apply concat_len.
{ rewrite <- (transpose_len Ha). rewrite map_length. lia. }

clear - Ha.
apply (transpose_map_Forall Ha).
intros v l Henc.
fold ty_size.
destruct (encode elem_ty v); try discriminate Henc.
simpl in Henc.
destruct (length l2 =? ty_size elem_ty) eqn:E; try discriminate Henc.
inversion Henc.
rewrite <- H0.
apply EqNat.beq_nat_true_stt.
auto.
Qed.

Lemma array_props : Props t.
Proof.
split.
- auto.
- apply array_rt1.
- apply array_rt2.
- apply array_mono1.
- apply array_mono2.
- apply array_encode_len.
Qed.

End array.
