Require Import defs.
Require Import le.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive LeAbstractByte : AbstractByte -> AbstractByte -> Type :=
  | LUninit b : LeAbstractByte Uninit b
  | LNoProv x o : LeAbstractByte (Init x None) (Init x o)
  | LWithProv x p : LeAbstractByte (Init x (Some p)) (Init x (Some p)).

Lemma mk_le_abstract_byte (b1 b2 : AbstractByte) (p: le b1 b2) : LeAbstractByte b1 b2.
Proof.
destruct b1.
- apply LUninit.
- destruct b2.
-- unfold le in p. destruct o; destruct p.
-- unfold le in p.
destruct o.
--- destruct o0.
---- destruct p. rewrite H. rewrite H0. apply LWithProv.
---- destruct p.
--- rewrite p. apply LNoProv.
Qed.

Inductive LeList : list AbstractByte -> list AbstractByte -> Type :=
  | LEmpty : LeList [] []
  | LLe b1 b2 l1' l2' : LeList l1' l2' -> LeAbstractByte b1 b2 -> LeList (b1::l1') (b2::l2').

Lemma mk_le_list (l1 : list AbstractByte) : forall l2, le l1 l2 -> LeList l1 l2.
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