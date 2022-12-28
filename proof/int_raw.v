Require Import defs int_encoding.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.EqdepFacts.
Require Import List.
Require Import Ndigits.

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

Lemma rt1_uint_le (size: Size) (int: Int): (int_in_range int size Unsigned = true) -> decode_uint_le size (encode_uint_le size int) = int.
Proof.
intros H.
unfold decode_uint_le, encode_uint_le.
rewrite lemma1.
rewrite lemma4.
Abort.
