Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Require Import Init.Nat.
Require Import Lia.
Require Import Ndigits.
Import ListNotations.

Require Import defs.

Context `{ENDIANNESS : Endianness}.

Inductive IntervalResult (x start stop : Int): Type :=
 | IResLower : (x < start)%Z -> IntervalResult _ _ _
 | IResIn : (x >= start)%Z -> (x < stop)%Z -> IntervalResult _ _ _
 | IResHigher : (x >= stop)%Z -> IntervalResult _ _ _.

Lemma mk_interval_result (x start stop: Int) : (start < stop)%Z -> IntervalResult x start stop.
Proof.
intros p.
destruct (x >=? start)%Z eqn:E.
- assert (x >= start)%Z as A1. { lia. }
  destruct (x <? stop)%Z eqn:E2.
-- assert (x < stop)%Z as A2. { lia. }
   apply (IResIn _ _ _ A1 A2).
-- assert (x >= stop)%Z as A3. { lia. }
   apply (IResHigher _ _ _ A3).
- assert (x < start)%Z as A4. { lia. }
  apply (IResLower _ _ _ A4).
Qed.

Definition unsigned_stop (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

Lemma unsigned_stop_pos (size: Size) : (0 < (unsigned_stop size))%Z.
Proof. unfold unsigned_stop. lia. Qed.

Definition wrap (ascii: Ascii.ascii) : AbstractByte :=
  let byte := Ascii.byte_of_ascii ascii in
  Init byte None.

Definition encode_uint_be (size : Size) (i : Int) (p1: (i >= 0)%Z) (p2 : (i < (unsigned_stop size))%Z): list AbstractByte :=
  let n := Z.to_N i in
  let bytes := N2ByteV_sized size n in
  let bytes := Vector.to_list bytes in
  let bytes := map wrap bytes in
  bytes.

Definition encode_int_be (size: Size) (signedness: Signedness) (i : Int) : option (list AbstractByte) :=
  match signedness with
   | Unsigned =>
     let stop := unsigned_stop size in
     match mk_interval_result i 0%Z stop (unsigned_stop_pos size) with
       | IResLower _ _ _ _  => None
       | IResIn _ _ _ p1 p2 => Some (encode_uint_be size i p1 p2)
       | IResHigher _ _ _ _ => None
     end
   | Signed => None (* TODO *)
  end.

(* TODO cleanup *)
Definition my_rev (l: list AbstractByte) : list AbstractByte := rev l.

Definition encode_int2 (size: Size) (signedness: Signedness) (i : Int) : option (list AbstractByte) :=
  let bytes := (encode_int_be size signedness i) in
  match ENDIANNESS with
   | BigEndian => bytes
   | LittleEndian => option_map my_rev bytes
  end.

Definition encode_int (size: Size) (signedness: Signedness) (v: Value) : option (list AbstractByte) :=
 match v with
  | VInt x => encode_int2 size signedness x
  | _ => None
 end.

Definition decode_int (size: Size) (signedness: Signedness) (l: list AbstractByte) : option Value.
Admitted.
