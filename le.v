(*
Require Import defs.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

(* less-than or equally defined value *)
Definition le_val (v1 v2 : Value) : Prop :=
 match (v1, v2) with
  | (BoolVal x, BoolVal y) => x = y
  | (IntVal x, IntVal y) => x = y
  | _ => False
 end.

Definition le_abstract_byte (b1 b2 : AbstractByte) : Prop :=
  match (b1, b2) with
    | (Uninit, _) => True
    | (Init data1 None, Init data2 _) => data1=data2
    | (Init data1 (Some prov1), Init data2 (Some prov2)) => data1=data2 /\ prov1=prov2
    | _ => False
  end.

Fixpoint le_list (l1 l2 : list AbstractByte) : Prop :=
 match (l1, l2) with
   | (a::x,b::y) => (le_abstract_byte a b /\ le_list x y)
   | ([], []) => True
   |  _ => False
 end.

Definition le_opt (o1 o2 : option Value) : Prop :=
  match (o1, o2) with
    | (None, _) => True
    | (Some l, Some r) => le_val l r
    | _ => False
  end.


*)
