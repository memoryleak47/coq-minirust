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

(* uint *)

Lemma uint_le_encode_valid (size: Size) (int : Int) (H: int_in_range int size Unsigned = true) :
  length (encode_uint_le size int) = size.
Proof.
unfold encode_uint_le.
rewrite map_length.
rewrite Vector.length_to_list.
reflexivity.
Qed.

Lemma lemma8 (n: nat) : (2 ^ (N.of_nat n))%N = N.shiftl_nat 1 n.
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
  rewrite lemma8.
  assert (length (map Ascii.ascii_of_byte l) = size) as F. {
    rewrite (@map_length _ _ Ascii.ascii_of_byte).
    assumption.
  }
  rewrite <- F.
  apply (ByteV2N_upper_bound).
Qed.

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
Admitted.

(* int *)

Lemma lemma7 (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
  exists l, Some l = encode_int_le size signedness int.
Proof.
unfold encode_int_le.
rewrite H. simpl.
(* TODO clean this up *)
exists (match signedness with
    | Signed =>
        if (int >=? 0)%Z
        then encode_uint_le size int
        else
         encode_uint_le size
           (int + signed_offset size)%Z
    | Unsigned => encode_uint_le size int
    end).
reflexivity.
Qed.

Lemma lemma9 (int: Int) (size: Size) (H: int_in_range int size Signed = true) (H2 : (int >=? 0)%Z = true) :
  int_in_range int size Unsigned = true.
Proof.
unfold int_in_range.
unfold int_start, int_stop. rewrite H2.
simpl.
destruct (@destruct_int_in_range _ _ _ H) as [_ Hmax].
unfold int_stop in Hmax.
apply (proj2 (Z.ltb_lt int _)).
Admitted.

Lemma lemma10 (size: Size) (int: Int) (H1: (int >=? 0)%Z = false) (H2: int_in_range int size Signed = true) :
  int_in_range (int + signed_offset size)%Z size Unsigned = true.
Proof.
Admitted.

Lemma lemma11 (size: Size) (int: Int)
              (Hs0 : (int >= - 2 ^ (Z.of_nat size * 8 - 1))%Z) :
  true = (
        int + 2 ^ (Z.of_nat size * 8)
    >=? 2 ^ (Z.of_nat size * 8 - 1))%Z.
Admitted.

Lemma rt1_int_le (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
exists l, Some l = encode_int_le size signedness int /\
decode_int_le size signedness l = Some int.
Proof.
destruct signedness.
(* signed *)
- destruct (int >=? 0)%Z eqn:E.

(* signed, positive *)
-- exists (encode_uint_le size int).
unfold encode_int_le. rewrite H. simpl.
rewrite E.
split. { reflexivity. }
unfold decode_int_le.
rewrite (uint_le_encode_valid).
rewrite Nat.eqb_refl.
simpl.
f_equal.
replace ((decode_uint_le size (encode_uint_le size int) >=?
   2 ^ (Z.of_nat size * 8 - 1))%Z) with false.
apply rt1_uint_le.
apply (lemma9 _ _ H); lia.
rewrite rt1_uint_le.
destruct (destruct_int_in_range _ _ _ H).
unfold int_stop in H1.
lia.
apply (lemma9 _ _ H); lia.
apply (lemma9 _ _ H); lia.

(* signed, negative *)
-- exists (encode_uint_le size (int + signed_offset size)%Z).
split.
--- unfold encode_int_le. rewrite H,E. simpl. reflexivity.
--- unfold decode_int_le. simpl.
    rewrite rt1_uint_le.
    destruct (destruct_int_in_range _ _ _ (lemma10 _ _ E H)) as [H0 H1].
---- rewrite uint_le_encode_valid.
     rewrite Nat.eqb_refl.
     simpl. f_equal.
     replace (int + signed_offset size >=? 2 ^ (Z.of_nat size * 8 - 1))%Z with true.
     lia.
     destruct (destruct_int_in_range _ _ _ H) as [Hs0 Hs1].
     unfold int_start in Hs0.
     unfold signed_offset.
     apply lemma11.
     assumption.
     apply (lemma10 _ _ E H).
---- apply (lemma10 _ _ E H).

(* unsigned *)
- exists (encode_uint_le size int).
unfold encode_int_le. rewrite H. simpl.
split. { reflexivity. }
unfold decode_int_le.
rewrite (uint_le_encode_valid).
rewrite Nat.eqb_refl.
simpl.
f_equal.
apply rt1_uint_le.
assumption.
assumption.
Qed.

Lemma rt1_int (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
exists l, Some l = encode_int_raw size signedness int /\
decode_int_raw size signedness l = Some int.
Proof.
destruct ENDIANNESS eqn:E.
- destruct (rt1_int_le size signedness int H) as [l].
  exists l. unfold encode_int_raw,decode_int_raw. rewrite E. assumption.
- destruct (rt1_int_le size signedness int H) as [l].
  exists (rev l). unfold encode_int_raw,decode_int_raw. rewrite E.
  destruct H0 as [H0 H1].
  rewrite <- H0. simpl.
  split; try reflexivity.
  rewrite rev_involutive.
  assumption.
Qed.