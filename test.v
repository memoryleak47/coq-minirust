From Minirust.def Require Import defs encoding int_encoding utils.
Require Import Coq.Init.Byte List NArith ZArith.
Import ListNotations.

Record Assumptions := {
 A_PTR_SIZE : PTR_SIZE = 8;
 A_ENDIANNESS : ENDIANNESS = BigEndian;
 A_P : P = nat;
}.

Lemma prov (A: Assumptions) (n: nat) : P.
rewrite (A_P A).
apply n.
Qed.

Ltac exec A := repeat (
  simpl ||
  auto ||
  split ||
  unfold encode,encode_int,encode_int_raw ||
  rewrite (A_PTR_SIZE A) ||
  rewrite (A_ENDIANNESS A) ||
  rewrite (A_P A)
).

Lemma test_encode_int (A : Assumptions) :
(encode (TInt 1 Unsigned) (VInt 255%Z)) = Some [Init "255" None] /\
(encode (TInt 2 Signed) (VInt (-2)%Z)) = Some [Init "255" None; Init "254" None].
Proof. exec A. Qed.

Lemma test_bool (A: Assumptions) :
(* encode *)
(encode TBool (VBool true) = Some [Init "001" None]) /\
(encode TBool (VBool false) = Some [Init "000" None]) /\

(* decode *)
(decode TBool [Init "001" None]) = Some (VBool true) /\
(decode TBool [Init "000" None]) = Some (VBool false) /\
(decode TBool [Init "001" (Some (prov A 12))]) = Some (VBool true) /\
(decode TBool [Init "000" (Some (prov A 42))]) = Some (VBool false) /\

(* error *)
(encode TBool (VInt 12%Z)) = None /\
(decode TBool [Init "002" None]) = None /\
(decode TBool []) = None /\
(decode TBool [Init "001" None; Init "001" None]) = None /\
(decode TBool [Uninit]) = None.
Proof. exec A. Qed.
