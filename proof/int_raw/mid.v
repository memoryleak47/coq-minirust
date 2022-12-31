Require Import defs int_encoding low.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.
Require Import ZArith.
Require Import Lia.

(* TODO cleanup this file. There are a lot of things, that can be simplified using the basenum abstraction. *)

(* every other number relevant for `int_in_range` can be expressed neatly using basenum. *)
Definition basenum (size: Size) := (2 ^ (Z.of_nat size*8-1))%Z.

Lemma double_base {size: Size} (H: size > 0) :
  (2 ^ (Z.of_nat size * 8))%Z = ((basenum size) * 2)%Z.
Proof.
unfold basenum.
destruct (mk_var (Z.of_nat size * 8))%Z as [x Hx].
assert (x > 0)%Z as B. { lia. }
rewrite Hx. clear - x B.
destruct x; try (simpl; lia).
assert (2^(Z.pos p) = 2 * 2^(Z.pos p-1))%Z; try lia.
rewrite <- (Z.pow_succ_r 2); try lia.
replace (Z.succ (Z.pos p - 1))%Z with (Z.pos p); lia.
Qed.

Lemma start_to_base (size: Size) (signedness: Signedness) :
  int_start size signedness = match signedness with
  | Unsigned => 0%Z
  | Signed => (-(basenum size))%Z
  end.
Proof.
destruct signedness; unfold int_start.
- unfold basenum. reflexivity.
- reflexivity.
Qed.

Lemma stop_to_base (size: Size) (signedness: Signedness) :
  (size > 0) ->
  int_stop size signedness = match signedness with
  | Unsigned => ((basenum size) * 2)%Z
  | Signed => basenum size
  end.
Proof.
intros Hs.
destruct signedness; unfold int_stop,basenum.
- reflexivity.
- apply (double_base Hs).
Qed.

Lemma offset_to_base (size: Size) :
  (size > 0) ->
  signed_offset size = ((basenum size) * 2)%Z.
Proof.
apply double_base.
Qed.

Ltac to_base := repeat (
  unfold int_in_range ||
  (rewrite stop_to_base; try assumption) ||
  (rewrite start_to_base; try assumption) ||
  (rewrite offset_to_base; try assumption)
).

Ltac to_base_in x := repeat (
  unfold int_in_range in x ||
  (rewrite stop_to_base in x; try assumption) ||
  (rewrite start_to_base in x; try assumption) ||
  (rewrite offset_to_base in x; try assumption)
).

Lemma lemma2 (int: Int) (size: Size) (H: int_in_range int size Signed = true) (H2 : (int >=? 0)%Z = true) :
  (size > 0) ->
  int_in_range int size Unsigned = true.
Proof.
intros Hs.
to_base_in H.
to_base.
lia.
Qed.


Lemma lemma3 (size: Size) (int: Int) (H1: (int >=? 0)%Z = false) (H2: int_in_range int size Signed = true) (Hs: size > 0) :
  int_in_range (int + signed_offset size)%Z size Unsigned = true.
Proof.
to_base.
to_base_in H2.
lia.
Qed.

Lemma lemma4 (size: Size) (int: Int)
              (Hs0 : (int >= - 2 ^ (Z.of_nat size * 8 - 1))%Z) :
  true = (
        int + 2 ^ (Z.of_nat size * 8)
    >=? 2 ^ (Z.of_nat size * 8 - 1))%Z.
Proof.
rewrite (proj2 (Z.geb_le _ _)). { reflexivity. }
assert (2 ^ (Z.of_nat size * 8 - 1) <= (- 2 ^ (Z.of_nat size * 8 - 1))%Z + 2 ^ (Z.of_nat size * 8))%Z; cycle 1. { lia. }
destruct (mk_var (Z.of_nat size * 8))%Z as [x Hx]. rewrite Hx. clear - x.
destruct x; try (simpl; lia).
assert (2^(Z.pos p) = 2 * 2^(Z.pos p-1))%Z; try lia.
rewrite <- (Z.pow_succ_r 2); try lia.
replace (Z.succ (Z.pos p - 1))%Z with (Z.pos p); lia.
Qed.

Lemma lemma5 (d: Int) (size: Size) :
  (size > 0) ->
  ((d >=? int_stop size Signed)%Z = true) ->
  (int_in_range d size Unsigned = true) ->
  (int_in_range (d - signed_offset size)%Z size Signed) = true.
Proof.
intros Hs.
to_base.
lia.
Qed.

Lemma lemma6 (d: Int) (size: Size) :
  (size > 0) ->
  (int_in_range d size Unsigned = true) ->
  (d - signed_offset size >=? 0)%Z = false.
Proof.
intros Hs.
to_base.
lia.
Qed.

Lemma lemma7 (size: Size) (l: list byte) :
  (length l = size) ->
  (decode_uint_le size l >=? 0)%Z = true.
Proof.
intros H.
destruct (destruct_int_in_range (uint_le_decode_valid size l H)) as [H0 _].
to_base_in H0.
to_base.
lia.
Qed.

Lemma lemma8 (d: Int) (size: Size) :
  (size > 0) ->
  (d >=? int_stop size Signed)%Z = false ->
  (d >=? 0)%Z = true ->
  (int_in_range d size Signed) = true.
Proof.
intros Hs.
to_base.
lia.
Qed.

Lemma rt1_int_le (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
  (size > 0) ->
  exists l, Some l = encode_int_le size signedness int /\
  decode_int_le size signedness l = Some int.
Proof.
intros Hs.
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
apply (lemma2 _ _ H); try lia; try assumption.
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
    destruct (destruct_int_in_range (lemma3 _ _ E H Hs)) as [H0 H1].
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
     apply (lemma3 _ _ E H Hs).
---- apply (lemma3 _ _ E H Hs).

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

Lemma rt2_int_le (size: Size) (signedness: Signedness) (l: list byte) (H: length l = size) :
  (size > 0) ->
  exists int, Some int = decode_int_le size signedness l /\
  encode_int_le size signedness int = Some l.
Proof.
intros Hs.
destruct signedness; unfold decode_int_le,encode_int_le; simpl; rewrite H; rewrite Nat.eqb_refl; simpl.
- destruct ((decode_uint_le size l) >=? int_stop size Signed)%Z eqn:E'.

(* signed, negative *)
-- exists ((decode_uint_le size l) - signed_offset size)%Z.
   rewrite lemma5; try assumption; try (apply uint_le_decode_valid; assumption).
   rewrite lemma6; try (apply uint_le_decode_valid; assumption); try assumption.
   unfold int_stop in E'. rewrite E'.
   split. { reflexivity. }
   simpl. f_equal.
   assert (forall x y, x - y + y = x)%Z as F. { lia. }
   rewrite F.
   apply rt2_uint_le.
   assumption.

(* signed, positive *)
-- exists (decode_uint_le size l).
   rewrite lemma7; try assumption.
   rewrite lemma8; try (assumption || (apply lemma7; assumption)).
   unfold int_stop in E'. rewrite E'.
   split. { reflexivity. }
   simpl.
   rewrite rt2_uint_le.
--- reflexivity.
--- assumption.

(* unsigned *)
- exists (decode_uint_le size l).
  split. { reflexivity. }
  rewrite uint_le_decode_valid; try assumption.
  simpl.
  rewrite rt2_uint_le.
-- reflexivity.
-- assumption.
Qed.
