Require Import defs int_encoding.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import List.
Require Import Ndigits.

Lemma a(l: list Ascii.ascii): (map Ascii.ascii_of_byte (map Ascii.byte_of_ascii l)) = l.
Proof.
rewrite map_map.
replace (fun x => _) with (fun x : Ascii.ascii => x). { apply map_id. }
apply functional_extensionality_dep.
intros x.
rewrite Ascii.ascii_of_byte_of_ascii.
reflexivity.
Qed.

Lemma rt1_uint_le (size: Size) (int: Int): (int_in_range int size Unsigned = true) -> decode_uint_le size (encode_uint_le size int) = int.
Proof.
intros H.
unfold decode_uint_le, encode_uint_le.
rewrite a.
Abort.