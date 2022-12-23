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

Inductive IntervalResult : Type :=
 | IResLower : IntervalResult
 | IResIn : IntervalResult
 | IResHigher : IntervalResult.

Definition mk_interval_result (x start stop: Int) : IntervalResult :=
  match (x >=? start)%Z with
  | true => match (x <? stop)%Z with
    | true => IResIn
    | false => IResHigher
    end
  | false => IResLower
  end.

Definition unsigned_stop (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

Lemma unsigned_stop_pos (size: Size) : (0 < (unsigned_stop size))%Z.
Proof. unfold unsigned_stop. lia. Qed.

Definition wrap (ascii: Ascii.ascii) : AbstractByte :=
  let byte := Ascii.byte_of_ascii ascii in
  Init byte None.

Definition encode_uint_le (size : Size) (i : Int): list AbstractByte :=
  let n := Z.to_N i in
  let bytes := N2ByteV_sized size n in
  let bytes := Vector.to_list bytes in
  let bytes := map wrap bytes in
  bytes.

Definition encode_int_le (size: Size) (signedness: Signedness) (i : Int) : option (list AbstractByte) :=
  match signedness with
   | Unsigned =>
     let stop := unsigned_stop size in
     match mk_interval_result i 0%Z stop with
       | IResLower  => None
       | IResIn => Some (encode_uint_le size i)
       | IResHigher => None
     end
   | Signed => None (* TODO *)
  end.

(* TODO cleanup *)
Definition my_rev (l: list AbstractByte) : list AbstractByte := rev l.

Definition encode_int2 (size: Size) (signedness: Signedness) (i : Int) : option (list AbstractByte) :=
  let bytes := (encode_int_le size signedness i) in
  match ENDIANNESS with
   | BigEndian => option_map my_rev bytes
   | LittleEndian => bytes
  end.

Definition encode_int (size: Size) (signedness: Signedness) (v: Value) : option (list AbstractByte) :=
 match v with
  | VInt x => encode_int2 size signedness x
  | _ => None
 end.

Definition decode_int (size: Size) (signedness: Signedness) (l: list AbstractByte) : option Value.
Admitted.
