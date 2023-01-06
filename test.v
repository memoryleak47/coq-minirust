From Minirust.def Require Import defs encoding int_encoding utils.
Require Import Coq.Init.Byte List NArith ZArith.
Import ListNotations.

(* TODO can we guarantee cleanly that these axioms do not escape the test suite? *)
Axiom ptr_size8 : PTR_SIZE = 8.
Axiom endianness_big : ENDIANNESS = BigEndian.

Ltac exec := repeat (
  simpl ||
  auto ||
  split ||
  unfold encode,encode_int,encode_int_raw ||
  rewrite ptr_size8 ||
  rewrite endianness_big
).

Lemma test_encode_int :
(encode (TInt 1 Unsigned) (VInt 255%Z)) = Some [Init "255" None] /\
(encode (TInt 2 Signed) (VInt (-2)%Z)) = Some [Init "255" None; Init "254" None].
Proof. exec. Qed.
