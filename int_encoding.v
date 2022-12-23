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

Definition unsigned_stop (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

Definition signed_start (size: Size) : Int :=
   let size := Z.of_nat size in
  (-2^(size*8 - 1))%Z.

(* stop is exclusive! Hence |start| = |stop| *)
Definition signed_stop (size: Size) : Int :=
   let size := Z.of_nat size in
  ((2^(size*8 - 1)))%Z.

(* the value by which a negative signed number is offsetted, to become positive. *)
(* same value as unsigned_stop *)
Definition signed_offset (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

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
     match ((i >=? 0)%Z && (i <? stop)%Z) with
       | true => Some (encode_uint_le size i)
       | false => None
     end

   | Signed =>
     let start := signed_start size in
     let stop := signed_stop size in
     let offset := signed_offset size in
     match (i >=? 0)%Z with
      | true => match (i <? stop)%Z with
        | true => Some (encode_uint_le size i)
        | false => None
      end
      | false => match (i >=? start)%Z with
        | true => Some (encode_uint_le size (i + offset)%Z)
        | false => None
      end
    end
  end.


Definition encode_int2 (size: Size) (signedness: Signedness) (i : Int) : option (list AbstractByte) :=
  let bytes := (encode_int_le size signedness i) in
  match ENDIANNESS with
   | BigEndian => option_map (fun x => rev x) bytes (* this `fun` seems redundant, but it isn't *)
   | LittleEndian => bytes
  end.

Definition encode_int (size: Size) (signedness: Signedness) (v: Value) : option (list AbstractByte) :=
 match v with
  | VInt x => encode_int2 size signedness x
  | _ => None
 end.

Definition decode_int (size: Size) (signedness: Signedness) (l: list AbstractByte) : option Value.
Admitted.
