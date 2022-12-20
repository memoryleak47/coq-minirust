Require Import defs.
Require Import le.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

(* TODO fixup lemmas! *)
(* <= of vals *)

Inductive LeVal : Value -> Value -> Type :=
  | LValEq v : LeVal v v.

Lemma mk_le_val (v1 v2 : Value) (p: le_val v1 v2) : LeVal v1 v2.
Proof.
destruct v1 as [b1|b1]; destruct v2 as [b2|b2];
unfold le_val in p.
- rewrite p. apply LValEq.
- destruct p.
- destruct p.
- rewrite p. apply LValEq.
Qed.

Inductive LeOpt : option Value -> option Value -> Type :=
  | LNone o : LeOpt None o
  | LSome i1 i2 : (LeVal i1 i2) -> LeOpt (Some i1) (Some i2).

Lemma mk_le_opt (o1 o2 : option Value) (p: le_opt o1 o2) : LeOpt o1 o2.
Proof.
destruct o1.
- destruct o2.
-- unfold le_opt in p. destruct (mk_le_val _ _ p).
--- apply LSome. apply mk_le_val. assumption.
-- unfold le_opt in p. destruct p.
- apply LNone.
Qed.

(* <= of byte lists *)

Inductive LeAbstractByte : AbstractByte -> AbstractByte -> Type :=
  | LUninit b : LeAbstractByte Uninit b
  | LNoProv x o : LeAbstractByte (Init x None) (Init x o)
  | LWithProv x p : LeAbstractByte (Init x (Some p)) (Init x (Some p)).

Lemma mk_le_abstract_byte (b1 b2 : AbstractByte) (p: le_abstract_byte b1 b2) : LeAbstractByte b1 b2.
Proof.
destruct b1.
- apply LUninit.
- destruct b2.
-- unfold le_abstract_byte in p. destruct o; destruct p.
-- unfold le_abstract_byte in p.
destruct o.
--- destruct o0.
---- destruct p. rewrite H. rewrite H0. apply LWithProv.
---- destruct p.
--- rewrite p. apply LNoProv.
Qed.

Inductive LeList : list AbstractByte -> list AbstractByte -> Type :=
  | LEmpty : LeList [] []
  | LLe b1 b2 l1' l2' : LeList l1' l2' -> LeAbstractByte b1 b2 -> LeList (b1::l1') (b2::l2').

Lemma mk_le_list (l1 : list AbstractByte) : forall l2, le_list l1 l2 -> LeList l1 l2.
Proof.
induction l1 as [|b1 l1' H].
- intros l2 p. destruct l2 as [|b2 l2'].
-- apply LEmpty; reflexivity.
-- destruct p.
- intros l2 p. destruct l2 as [|b2 l2'].
--  destruct p.
-- apply LLe.
--- apply H. destruct p. assumption.
--- destruct p. apply mk_le_abstract_byte. assumption.
Qed.

(* decoding *)

Inductive DecodeBool : list AbstractByte -> Type :=
 | DBoolTrue o : DecodeBool [Init x01 o]
 | DBoolFalse o : DecodeBool [Init x00 o]
 | DBoolInvalid l : (decode BoolTy l = None) -> DecodeBool l.

Lemma mk_decode_bool (l: list AbstractByte) : DecodeBool l.
Proof.
destruct l.
- apply DBoolInvalid. auto.
- destruct l.
-- destruct a.
--- apply DBoolInvalid. auto.
--- destruct b; try (apply DBoolInvalid; unfold decode; reflexivity).
---- apply DBoolFalse.
---- apply DBoolTrue.
-- apply DBoolInvalid.
unfold decode. destruct a.
--- reflexivity.
--- destruct b; reflexivity.
Qed.

(* deprecated: *)

Lemma obvious (l: list AbstractByte) : le_list l l.
Proof.
induction l.
- unfold le_list. auto.
- unfold le_list. split.
-- destruct a.
--- unfold le_abstract_byte. auto.
--- unfold le_abstract_byte.
    destruct o. auto. auto.
-- auto.
Qed.

Lemma le_list_helper (l1 : list AbstractByte) : forall l2, le_list l1 l2 -> length l1 = length l2.
Proof.
induction l1 as [|b1 l1' H].
- intros l2 p. destruct l2 as [|b2 l2'].
-- reflexivity.
-- destruct p.
- intros l2 p. destruct l2 as [|b2 l2'].
-- destruct p.
-- simpl. f_equal.
apply H. destruct p as [A B].
assumption.
Qed.
