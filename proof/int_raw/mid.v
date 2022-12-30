Require Import defs int_encoding low.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.
Require Import ZArith.
Require Import Lia.

(* TODO unused *)
Lemma lemma1 (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
  exists l, Some l = encode_int_le size signedness int.
Proof.
unfold encode_int_le.
rewrite H. simpl.
destruct signedness, (int >=? 0)%Z.
- exists (encode_uint_le size int). reflexivity.
- exists (encode_uint_le size (int + signed_offset size)%Z). reflexivity.
- exists (encode_uint_le size int). reflexivity.
- exists (encode_uint_le size int). reflexivity.
Qed.

Lemma z_to_nat_exp (n: nat) : (2 ^ Z.of_nat n)%Z = Z.of_nat (2 ^ n).
Proof.
induction n as [|n IH].
- reflexivity.
- rewrite Nat.pow_succ_r.
  replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)); cycle 1. { lia. }
  rewrite Z.pow_succ_r; try lia.
lia.
Qed.

Lemma lemma2 (int: Int) (size: Size) (H: int_in_range int size Signed = true) (H2 : (int >=? 0)%Z = true) :
  int_in_range int size Unsigned = true.
Proof.
unfold int_in_range.
unfold int_start, int_stop. rewrite H2.
simpl.
destruct (destruct_int_in_range H) as [_ Hbase].
unfold int_stop in Hbase.
apply (proj2 (Z.ltb_lt int _)).
apply (Z.lt_trans _ _ _ Hbase). clear - size.
destruct size. { simpl. lia. } (* this gives me size > 0 *)
assert ((Z.of_nat (S size) * 8)%Z = Z.of_nat ((S size) * 8)) as A. { lia. }
rewrite A. clear A.
assert ((Z.of_nat ((S size) * 8) - 1)%Z = Z.of_nat ((S size) * 8 - 1)) as A. { lia. }
rewrite A. clear A.
do 2 rewrite z_to_nat_exp.
apply inj_lt.
apply Nat.pow_lt_mono_r. { lia. }
lia.
Qed.

Lemma lemma3 (size: Size) (int: Int) (H1: (int >=? 0)%Z = false) (H2: int_in_range int size Signed = true) :
  int_in_range (int + signed_offset size)%Z size Unsigned = true.
Proof.
unfold int_in_range. destruct (destruct_int_in_range H2).
Admitted.

Lemma lemma4 (size: Size) (int: Int)
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
apply (lemma2 _ _ H); lia.
rewrite rt1_uint_le.
destruct (destruct_int_in_range H).
unfold int_stop in H1.
lia.
apply (lemma2 _ _ H); lia.
apply (lemma2 _ _ H); lia.

(* signed, negative *)
-- exists (encode_uint_le size (int + signed_offset size)%Z).
split.
--- unfold encode_int_le. rewrite H,E. simpl. reflexivity.
--- unfold decode_int_le. simpl.
    rewrite rt1_uint_le.
    destruct (destruct_int_in_range (lemma3 _ _ E H)) as [H0 H1].
---- rewrite uint_le_encode_valid.
     rewrite Nat.eqb_refl.
     simpl. f_equal.
     replace (int + signed_offset size >=? 2 ^ (Z.of_nat size * 8 - 1))%Z with true.
     lia.
     destruct (destruct_int_in_range H) as [Hs0 Hs1].
     unfold int_start in Hs0.
     unfold signed_offset.
     apply lemma4.
     assumption.
     apply (lemma3 _ _ E H).
---- apply (lemma3 _ _ E H).

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