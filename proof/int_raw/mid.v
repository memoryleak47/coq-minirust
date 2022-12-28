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

Lemma lemma2 (int: Int) (size: Size) (H: int_in_range int size Signed = true) (H2 : (int >=? 0)%Z = true) :
  int_in_range int size Unsigned = true.
Proof.
unfold int_in_range.
unfold int_start, int_stop. rewrite H2.
simpl.
destruct (@destruct_int_in_range _ _ _ H) as [_ Hmax].
unfold int_stop in Hmax.
apply (proj2 (Z.ltb_lt int _)).
Admitted.

Lemma lemma3 (size: Size) (int: Int) (H1: (int >=? 0)%Z = false) (H2: int_in_range int size Signed = true) :
  int_in_range (int + signed_offset size)%Z size Unsigned = true.
Proof.
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
destruct (destruct_int_in_range _ _ _ H).
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
    destruct (destruct_int_in_range _ _ _ (lemma3 _ _ E H)) as [H0 H1].
---- rewrite uint_le_encode_valid.
     rewrite Nat.eqb_refl.
     simpl. f_equal.
     replace (int + signed_offset size >=? 2 ^ (Z.of_nat size * 8 - 1))%Z with true.
     lia.
     destruct (destruct_int_in_range _ _ _ H) as [Hs0 Hs1].
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
