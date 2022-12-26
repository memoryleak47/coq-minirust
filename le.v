Require Import defs.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

Class DefinedRelation (T : Type) := {
  le : T -> T -> Prop
}.

Global Instance AbstractByte_DefinedRelation : DefinedRelation AbstractByte := {
  le x y :=
    match (x, y) with
    | (Uninit, _) => True
    | (Init data1 None, Init data2 _) => data1=data2
    | (Init data1 (Some prov1), Init data2 (Some prov2)) => data1=data2 /\ prov1=prov2
    | _ => False
    end
}.

Global Instance list_DefinedRelation (T: Type) {_: DefinedRelation T} : DefinedRelation (list T) := {
  le x y :=
    let f := fix f (x y: list T) :=
    match (x, y) with
    | (a::l1,b::l2) => (le a b /\ f l1 l2)
    | ([], []) => True
    |  _ => False
    end
    in

    f x y
}.

Global Instance option_DefinedRelation (T: Type) {_: DefinedRelation T} : DefinedRelation (option T) := {
  le x y :=
    match (x, y) with
    | (None, _) => True
    | (Some l, Some r) => le l r
    | _ => False
    end
}.

Global Instance Pointer_DefinedRelation : DefinedRelation (Int * option P) := {
  le x y :=
    let addr := fst x in
    let addr' := fst y in
    let prov := snd x in
    let prov' := snd y in

    let a := addr = addr' in
    let b :=
      match (prov, prov') with
      | (None, _) => True
      | (Some p, Some p') => (P_EQ p p') = true
      | _ => False
      end
    in

    a /\ b
}.

Global Instance Value_DefinedRelation : DefinedRelation Value := {
  le x y :=
    match (x, y) with
    | (VBool x, VBool y) => x = y
    | (VInt x, VInt y) => x = y
    | _ => False
    end
}.
