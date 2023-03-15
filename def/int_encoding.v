Require Import Bool Datatypes Coq.Init.Byte ZArith List Init.Nat Lia Ndigits.
Import ListNotations.

From Minirust.def Require Import ty utils.

Section int_encoding.

Context {memory: Memory}.

(* fundamentals *)

Definition int_start (size: Size) (signedness: Signedness) : Int :=
  let size := Z.of_nat size in
  match signedness with
  | Unsigned => 0%Z
  | Signed => (-2^((size*8) - 1))%Z
  end.

(* stop is exclusive! *)
Definition int_stop (size: Size) (signedness: Signedness) : Int :=
  let size := Z.of_nat size in
  match signedness with
  | Unsigned => (2^(size*8))%Z
  | Signed => (2^((size*8) - 1))%Z
  end.

Definition int_in_range (i: Int) (size: Size) (signedness: Signedness) : bool :=
  let start := int_start size signedness in
  let stop := int_stop size signedness in
  (i >=? start)%Z && (i <? stop)%Z.

(* the value by which a negative signed number is offsetted, to become positive. *)
Definition signed_offset (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

(* encode *)

(* assumes that i is in range *)
Definition encode_uint_le (size : Size) (i : Int): list byte :=
  let n := Z.to_N i in
  let bytes := N2ByteV_sized size n in
  let bytes := Vector.to_list bytes in
  let bytes := map Ascii.byte_of_ascii bytes in
  bytes.

Definition encode_int_le (size: Size) (signedness: Signedness) (i : Int) : option (list byte) :=
  Some (
    match signedness with
    | Unsigned => encode_uint_le size i
    | Signed =>
      if (i >=? 0)%Z then
        encode_uint_le size i
      else
        let offset := signed_offset size in
        encode_uint_le size (i + offset)%Z
    end
  )
  >>= assuming_const (int_in_range i size signedness).

Definition encode_int_raw (size: Size) (signedness: Signedness) (i : Int) : option (list byte) :=
  let bytes := (encode_int_le size signedness i) in
  match ENDIANNESS with
  | BigEndian => bytes o-> (fun x => rev x) (* this `fun` seems redundant, but it isn't *)
  | LittleEndian => bytes
  end.

(* decode *)

Definition decode_uint_le (size: Size) (bytes: list byte): Int :=
  let bytes := map Ascii.ascii_of_byte bytes in
  let bytes := Vector.of_list bytes in
  let n := ByteV2N bytes in

  Z.of_N n.

Definition decode_int_le (size: Size) (signedness: Signedness) (l: list byte) : option Int :=
  Some (
    let i := decode_uint_le size l in
    match signedness with
    | Unsigned => i
    | Signed =>
      let stop := int_stop size Signed in
      if (i >=? stop)%Z then
        let offset := signed_offset size in
        (i - offset)%Z
      else
        i
    end
  )
  >>= assuming_const (length l =? size).

Definition decode_int_raw (size: Size) (signedness: Signedness) (l: list byte) : option Int :=
  let l :=
    match ENDIANNESS with
    | BigEndian => rev l
    | LittleEndian => l
    end in

  decode_int_le size signedness l.

End int_encoding.