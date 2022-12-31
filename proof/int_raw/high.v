Require Import defs int_encoding mid.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.
Require Import ZArith.
Require Import Lia.

(* encode yes, no *)

Lemma encode_int_yes {size: Size} {signedness: Signedness} {int: Int} (H: int_in_range int size signedness = true) :
  exists l, Some l = encode_int_raw size signedness int /\ length l = size.
Proof.
Admitted.

Lemma encode_int_no {size: Size} {signedness: Signedness} {int: Int} (H: int_in_range int size signedness = false) :
  encode_int_raw size signedness int = None.
Proof.
Admitted.

(* decode yes, no *)
Lemma decode_int_yes {size: Size} {signedness: Signedness} {l: list byte} (H: length l = size) :
  exists i, Some i = decode_int_raw size signedness l /\ int_in_range i size signedness = true.
Proof.
Admitted.

Lemma decode_int_no {size: Size} {signedness: Signedness} {l: list byte} (H: length l <> size) :
  decode_int_raw size signedness l = None.
Proof.
Admitted.

(* roundtrip properties *)

Lemma rt1_int (size: Size) (signedness: Signedness) (int: Int) (H: int_in_range int size signedness = true) :
  (size > 0) ->
  exists l, Some l = encode_int_raw size signedness int /\
  decode_int_raw size signedness l = Some int.
Proof.
intros Hs.
destruct ENDIANNESS eqn:E.
- destruct (rt1_int_le size signedness int H) as [l]; try assumption.
  exists l. unfold encode_int_raw,decode_int_raw. rewrite E. assumption.
- destruct (rt1_int_le size signedness int H) as [l]; try assumption.
  exists (rev l). unfold encode_int_raw,decode_int_raw. rewrite E.
  destruct H0 as [H0 H1].
  rewrite <- H0. simpl.
  split; try reflexivity.
  rewrite rev_involutive.
  assumption.
Qed.

Lemma rt2_int (size: Size) (signedness: Signedness) (l: list byte) (H: length l = size) :
  (size > 0) ->
  exists i, Some i = decode_int_raw size signedness l /\
  encode_int_raw size signedness i = Some l.
Proof.
intros Hs.
destruct ENDIANNESS eqn:E.
- destruct (rt2_int_le size signedness l H) as [i]; try assumption.
  exists i. unfold encode_int_raw,decode_int_raw. rewrite E. assumption.
- assert (length (rev l) = size) as H'. { rewrite rev_length. assumption. }
  destruct (rt2_int_le size signedness (rev l) H') as [i]; try assumption.
  exists i. unfold encode_int_raw,decode_int_raw. rewrite E.
  destruct H0 as [H0 H1].
  rewrite <- H0.
  split. { reflexivity. }
  rewrite H1.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.