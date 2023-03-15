From Minirust.def Require Import ty encoding int_encoding utils.
Require Import Coq.Init.Byte List NArith ZArith Lia.
Import ListNotations.

Lemma ptr_size_gt0 : 8 > 0. lia. Qed.

Local Instance TestMemory : Memory := {
  PTR_SIZE := 8;
  ENDIANNESS := BigEndian;
  P := nat;
  P_EQ := Nat.eqb;
  P_EQ_REFLECT := Nat.eqb_spec;
  PTR_SIZE_GT0 := ptr_size_gt0;
}.

Ltac exec := repeat (
  simpl ||
  auto ||
  split ||
  unfold encode,encode_int,decode_int,decode_int_raw,encode_int_raw,encode_array,decode_array
).

Lemma test_int :
(* encode *)
(encode (TInt 1 Unsigned) (VInt 255%Z)) = Some [Init "255" None] /\
(encode (TInt 2 Signed) (VInt (-1)%Z)) = Some [Init "255" None; Init "255" None] /\
(encode (TInt 2 Unsigned) (VInt 42%Z)) = Some [Init "000" None; Init "042" None] /\
(encode (TInt 2 Unsigned) (VInt 258%Z)) = Some [Init "001" None; Init "002" None] /\

(* decode *)
(decode (TInt 2 Unsigned) [Init "000" None; Init "001" None]) = Some (VInt 1%Z) /\
(decode (TInt 2 Unsigned) [Init "001" None; Init "000" None]) = Some (VInt 256%Z) /\
(decode (TInt 2 Unsigned) [Init "000" (Some 12); Init "000" None]) = Some (VInt 0%Z) /\

(* error *)
(decode (TInt 2 Unsigned) [Init "000" None]) = None.
Proof. exec. Qed.

Lemma test_bool :
(* encode *)
(encode TBool (VBool true) = Some [Init "001" None]) /\
(encode TBool (VBool false) = Some [Init "000" None]) /\

(* decode *)
(decode TBool [Init "001" None]) = Some (VBool true) /\
(decode TBool [Init "000" None]) = Some (VBool false) /\
(decode TBool [Init "001" (Some 12)]) = Some (VBool true) /\
(decode TBool [Init "000" (Some 42)]) = Some (VBool false) /\

(* error *)
(encode TBool (VInt 12%Z)) = None /\
(decode TBool [Init "002" None]) = None /\
(decode TBool []) = None /\
(decode TBool [Init "001" None; Init "001" None]) = None /\
(decode TBool [Uninit]) = None.
Proof. exec. Qed.

Lemma test_array :
(* encode *)
encode (TArray (TInt 2 Unsigned) 2%Z) (VTuple [VInt 12%Z; VInt 13%Z]) = Some [Init "000" None; Init "012" None; Init "000" None; Init "013" None]  /\
decode (TArray (TInt 2 Unsigned) 2%Z) [Init "000" None; Init "012" None; Init "000" None; Init "013" None] = Some (VTuple [VInt 12%Z; VInt 13%Z]) /\

(* decode *)
encode (TArray TBool 0%Z) (VTuple []) = Some [] /\
decode (TArray TBool 0%Z) [] = Some (VTuple []) /\

(* error *)
encode (TArray TBool 1%Z) (VTuple []) = None /\
decode (TArray TBool 1%Z) [] = None.
Proof. exec. Qed.

Notation tu := (TUnion [] [(0, 2); (3, 1)] 4).
Lemma test_union :
encode tu (VUnion [[Uninit; Init x01 None]; [Init x02 None]]) = Some [Uninit; Init x01 None; Uninit; Init x02 None] /\
decode tu [Init x01 None; Init x01 None; Init x01 None; Init x01 None] = Some (VUnion [[Init x01 None; Init x01 None]; [Init x01 None]]).
Proof. exec. Qed.

Notation tt := (TTuple [(1, TBool); (3, TBool)] 4).
Lemma test_tuple :
encode tt (VTuple [VBool true; VBool false]) = Some [Uninit; Init x01 None; Uninit; Init x00 None] /\
decode tt [Init x01 None; Init x01 None; Init x01 None; Init x01 None] = Some (VTuple [VBool true; VBool true]).
Proof. exec. Qed.
