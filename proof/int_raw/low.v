Require Import defs int_encoding.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.
Require Import ZArith.
Require Import Lia.

Lemma lemma1 (l: list Ascii.ascii): (map Ascii.ascii_of_byte (map Ascii.byte_of_ascii l)) = l.
Proof.
rewrite map_map.
replace (fun x => _) with (fun x : Ascii.ascii => x). { apply map_id. }
apply functional_extensionality_dep.
intros x.
rewrite Ascii.ascii_of_byte_of_ascii.
reflexivity.
Qed.

Lemma lemma2 {T:Type} (n: nat) (v: Vector.t T n) (P:n=n): eq_rect n (Vector.t T) v n P = v.
Proof.
rewrite <- Eqdep_dec.eq_rect_eq_dec.
reflexivity. intros x y.
apply PeanoNat.Nat.eq_dec.
Qed.

Lemma lemma3 {T O : Type} (n m:nat) (v:Vector.t T n) (f: forall n, Vector.t T n -> O) (P : n=m):
f n v = f m (eq_rect n (Vector.t T) v m P).
Proof.
rewrite <- P.
rewrite lemma2.
reflexivity.
Qed.

Lemma lemma4 {T O: Type} (n:nat) (v:Vector.t T n) (f : forall n, Vector.t T n -> O) :
f _ (Vector.of_list (Vector.to_list v)) = f n v.
rewrite (lemma3 (length _) n _ _ (Vector.length_to_list _ _ _)).
rewrite Vector.of_list_to_list_opp.
reflexivity.
Qed.

Lemma lemma5_2 (n: nat) (v: Vector.t bool (S n)) :
  exists h t, v = Vector.cons bool h n t.
Proof.
induction n,v using Vector.caseS.
- exists h, v. reflexivity.
Qed.

Lemma lemma5 (n: nat) (v: Vector.t bool (n*8)): ByteVector.to_Bvector (ByteVector.of_Bvector v) = v.
Proof.
induction n as [|n IH].
- simpl in v.
  apply Vector.case0.
  simpl. reflexivity.
- simpl in v.
  destruct (lemma5_2 _ v) as [b0 [v0 H]]. rewrite H. clear v H.
  destruct (lemma5_2 _ v0) as [b1 [v1 H]]. rewrite H. clear v0 H.
  destruct (lemma5_2 _ v1) as [b2 [v2 H]]. rewrite H. clear v1 H.
  destruct (lemma5_2 _ v2) as [b3 [v3 H]]. rewrite H. clear v2 H.
  destruct (lemma5_2 _ v3) as [b4 [v4 H]]. rewrite H. clear v3 H.
  destruct (lemma5_2 _ v4) as [b5 [v5 H]]. rewrite H. clear v4 H.
  destruct (lemma5_2 _ v5) as [b6 [v6 H]]. rewrite H. clear v5 H.
  destruct (lemma5_2 _ v6) as [b7 [v7 H]]. rewrite H. clear v6 H.
  simpl.
  rewrite IH.
  auto.
Qed.

Lemma lemma7 (n: nat) : (2 ^ (N.of_nat n))%N = N.shiftl_nat 1 n.
induction n as [|n IH].
- reflexivity.
- replace ((2 ^ N.of_nat (S n))%N) with (2 * (2 ^ N.of_nat n))%N.
  replace (N.shiftl_nat 1 (S n))%N with (2 * (N.shiftl_nat 1 n))%N.
-- f_equal. assumption.
-- replace (2 * N.shiftl_nat 1 n)%N with (N.shiftl_nat 1 n * 2)%N; try lia.
   simpl. lia.
-- rewrite <- N.pow_succ_r'.
   lia.
Qed.

Lemma lemma8 (n: nat) (v: Vector.t bool n) (k: nat) : Bv2N (Vector.append v (Bvector.Bvect_false k)) = Bv2N v.
Proof.
Admitted.

Lemma lemma6 (size: Size) (n: N) (H: (n < Z.to_N (int_stop size Unsigned))%N) : Bv2N (N2Bv_sized (size * 8) n) = n.
Proof.
assert (size*8 >= N.size_nat n) as H2. { admit. }
assert (exists k, size*8 = N.size_nat n + k) as H3. {
  exists (size*8 - N.size_nat n). lia.
}
clear H2.
destruct H3 as [k Hk].
rewrite Hk.
rewrite (N2Bv_N2Bv_sized_above n k).
rewrite lemma8.
apply Bv2N_N2Bv.
Admitted.

Lemma destruct_int_in_range (i: Int) (size: Size) (signed: Signedness) (P: int_in_range i size signed = true) :
(i >= int_start size signed)%Z /\ (i < int_stop size signed)%Z.
Proof.
unfold int_in_range in P.
lia.
Qed.

(* input validity *)

Lemma uint_le_encode_valid (size: Size) (int : Int) (H: int_in_range int size Unsigned = true) :
  length (encode_uint_le size int) = size.
Proof.
unfold encode_uint_le.
rewrite map_length.
rewrite Vector.length_to_list.
reflexivity.
Qed.

Lemma uint_le_decode_valid (size: Size) (l: list byte) (H: length l = size) :
  int_in_range (decode_uint_le size l) size Unsigned = true.
Proof.
unfold decode_uint_le.
unfold int_in_range.
simpl.
assert (forall x, Z.of_N x >=? 0 = true)%Z as E. {
  intros x.
  apply (proj2 (Z.geb_le (Z.of_N x) 0)).
  lia.
}
rewrite E. simpl. clear E.
apply (proj2 (Z.ltb_lt (Z.of_N _) _)).
replace (2 ^ (Z.of_nat size * 8))%Z with (Z.of_N (2 ^ ((N.of_nat size) * 8))); try lia.
- apply (proj1 (N2Z.inj_lt (ByteV2N _) _)).
  replace (N.of_nat size * 8)%N with (N.of_nat (size * 8)); try lia.
  rewrite lemma7.
  assert (length (map Ascii.ascii_of_byte l) = size) as F. {
    rewrite (@map_length _ _ Ascii.ascii_of_byte).
    assumption.
  }
  rewrite <- F.
  apply (ByteV2N_upper_bound).
Qed.

(* round-trip properties *)

Lemma rt1_uint_le (size: Size) (int: Int) (H: int_in_range int size Unsigned = true) :
  decode_uint_le size (encode_uint_le size int) = int.
Proof.
unfold decode_uint_le, encode_uint_le.
rewrite lemma1.
rewrite lemma4.
unfold ByteV2N.
unfold N2ByteV_sized.
unfold Basics.compose.
rewrite lemma5.
destruct (destruct_int_in_range _ _ _ H) as [H0 H1].
unfold int_start in H0.
rewrite lemma6.
- rewrite Znat.Z2N.id. { reflexivity. }
  lia.
- apply Z2N.inj_lt.
-- lia.
-- unfold int_stop. lia.
-- assumption.
Qed.

Lemma rt2_uint_le (size: Size) (l: list byte) (P: length l = size) :
  encode_uint_le size (decode_uint_le size l) = l.
Proof.
unfold encode_uint_le, decode_uint_le.
rewrite N2Z.id.
unfold ByteV2N.
unfold N2ByteV_sized.
unfold Basics.compose.
Admitted.
