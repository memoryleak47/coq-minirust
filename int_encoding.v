Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Require Import Init.Nat.
Require Import Lia.
Import ListNotations.

Require Import defs.

Context `{ENDIANNESS : Endianness}.

Inductive IntervalResult (x start stop : Int): Type :=
 | IResLower : (x < start)%Z -> IntervalResult _ _ _
 | IResIn : (x >= start)%Z -> (x < stop)%Z -> IntervalResult _ _ _
 | IResHigher : (x >= stop)%Z -> IntervalResult _ _ _.

Definition mk_interval_result (x start stop: Int) : (* (start < stop)%Z -> *) IntervalResult x start stop.
Admitted.

Definition unsigned_stop (size: Size) : Int :=
  let size := Z.of_nat size in
  (2^(size*8))%Z.

Definition encode_uint_be (size : Size) (i : Int) (p1: (i >= 0)%Z) (p2 : (i < (unsigned_stop size))%Z): option (list AbstractByte). Admitted.

Definition encode_int_be (int_ty : IntTy) (i : Int) : option (list AbstractByte) :=
  match i_signedness int_ty with
   | Unsigned =>
     let stop := unsigned_stop (i_size int_ty) in
     match mk_interval_result i 0%Z stop with
       | IResLower _ _ _ _  => None
       | IResIn _ _ _ p1 p2 => encode_uint_be (i_size int_ty) i p1 p2 
       | IResHigher _ _ _ _ => None
     end
   | Signed => None (* TODO *)
  end.

(* TODO cleanup *)
Definition my_rev (l: list AbstractByte) : list AbstractByte := rev l.

Definition encode_int2 (int_ty : IntTy) (i : Int) : option (list AbstractByte) :=
  let bytes := (encode_int_be int_ty i) in
  match ENDIANNESS with
   | BigEndian => bytes
   | LittleEndian => option_map my_rev bytes
  end.

Definition encode_int (int_ty: IntTy) (v: Value) : option (list AbstractByte) :=
 match v with
  | VInt x => encode_int2 int_ty x
  | _ => None
 end.

Definition decode_int (int_ty: IntTy) (l: list AbstractByte) : option Value.
Admitted.