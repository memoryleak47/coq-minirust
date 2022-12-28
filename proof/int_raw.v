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

Lemma lemma5 (n:nat) (v: Vector.t bool (n*8)) :
  ByteVector.to_Bvector (ByteVector.of_Bvector v) = v.
Proof.
Admitted.

Lemma lemma6 (size: Size) (v: BinNums.N) : Bv2N (N2Bv_sized (size * 8) v) = v.
Proof.
Admitted.

Lemma destruct_int_in_range (i: Int) (size: Size) (signed: Signedness) (P: int_in_range i size signed = true) :
(i >= int_start size signed)%Z /\ (i < int_stop size signed)%Z.
Proof.
unfold int_in_range in P.
lia.
Qed.

Lemma rt1_uint_le (size: Size) (int: Int): (int_in_range int size Unsigned = true) -> decode_uint_le size (encode_uint_le size int) = int.
Proof.
intros H.
unfold decode_uint_le, encode_uint_le.
rewrite lemma1.
rewrite lemma4.
unfold ByteV2N.
unfold N2ByteV_sized.
unfold Basics.compose.
rewrite lemma5.
rewrite lemma6.
rewrite Znat.Z2N.id. { reflexivity. }
destruct (destruct_int_in_range _ _ _ H).
unfold int_start in H0. lia.
Qed.

Lemma rt2_uint_le (size: Size) (l: list byte) (P: length l = size) :
  encode_uint_le size (decode_uint_le size l) = l.
Proof.
unfold encode_uint_le, decode_uint_le.
rewrite N2Z.id.
unfold ByteV2N.
unfold N2ByteV_sized.
unfold Basics.compose.
Abort.
