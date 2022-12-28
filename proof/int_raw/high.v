Require Import defs int_encoding mid.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.
Require Import ZArith.
Require Import Lia.

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
