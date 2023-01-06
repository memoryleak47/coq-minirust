Require Import Datatypes List.
Import ListNotations.

From Minirust.def Require Import defs.

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

Definition le_list (T: Type) (x y : list T) (elem_f: T -> T -> Prop) : Prop :=
  let f := fix f (x y : list T) :=
    match (x, y) with
    | (a::l1,b::l2) => (elem_f a b /\ f l1 l2)
    | ([],[]) => True
    | _ => False
    end
  in

  f x y.

Global Instance list_DefinedRelation (T: Type) (_: DefinedRelation T) : DefinedRelation (list T) := {
  le x y := le_list T x y le
}.

Global Instance option_DefinedRelation (T: Type) (_: DefinedRelation T) : DefinedRelation (option T) := {
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
    let addr2 := fst y in
    let prov := snd x in
    let prov2 := snd y in

    let a := addr = addr2 in
    let b :=
      match (prov, prov2) with
      | (None, _) => True
      | (Some p, Some p2) => (P_EQ p p2) = true
      | _ => False
      end
    in

    a /\ b
}.

Global Instance Value_DefinedRelation : DefinedRelation Value := {
  le x y :=
    let f := fix f (x y : Value) :=
      match (x, y) with
      | (VInt x, VInt y) => x = y
      | (VBool x, VBool y) => x = y
      | (VPtr addr prov, VPtr addr' prov') => le (addr, prov) (addr', prov')
      | (VTuple vals, VTuple vals') => le_list Value vals vals' f
      | (VUnion chunks, VUnion chunks') => le chunks chunks'
      | _ => False
      end
    in

    f x y
}.