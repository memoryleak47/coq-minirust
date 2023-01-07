From Minirust.def Require Import ty le.
Require Import Datatypes Coq.Init.Byte List.
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
  | LLe b1 b2 l1' l2' : LeList l1' l2' -> LeAbstractByte b1 b2 -> le (b1::l1') (b2::l2') -> LeList (b1::l1') (b2::l2').

Lemma mk_le_list (l1 : list AbstractByte) : forall l2, le l1 l2 -> LeList l1 l2.
Proof.
induction l1 as [|b1 l1' H].
- intros l2 p. destruct l2 as [|b2 l2'].
-- apply LEmpty; reflexivity.
-- destruct p.
- intros l2 p.
  destruct l2 as [|b2 l2'].
--  destruct p.
-- apply LLe.
--- apply H. destruct p. assumption.
--- destruct p. apply mk_le_abstract_byte. assumption.
--- assumption.
Qed.

(* le refl *)

Lemma le_list_gen_refl {T: Type} (l : list T) {_: DefinedRelation T} (Q: forall (t: T), le t t) : le l l.
Proof.
simpl.
induction l as [|t l IH].
- simpl. trivial.
- simpl.
  split.
-- apply Q.
-- apply IH.
Qed.

Lemma le_option_gen_refl {T: Type} (o: option T) {_: DefinedRelation T} (Q: forall (t: T), le t t) : le o o.
Proof.
destruct o.
- apply Q.
- simpl. trivial.
Qed.

Lemma le_abstract_byte_refl (x : AbstractByte) : le x x.
Proof.
destruct x.
- simpl. trivial.
- destruct o.
-- simpl. auto.
-- simpl. auto.
Qed.

Lemma le_list_abstract_byte_refl (l : list AbstractByte) : le l l.
Proof.
apply (le_list_gen_refl l le_abstract_byte_refl).
Qed.

Fixpoint le_val_refl (v : Value) : le v v.
Proof.
destruct v eqn:E.
- simpl. reflexivity.
- simpl. reflexivity.
- destruct o;
  simpl;
  split;
  auto.
  apply (proj2 (p_eq p p)).
  reflexivity.

- generalize dependent v.
  induction l as [|t l IH].
-- simpl. trivial.
-- split.
--- apply le_val_refl.
--- eapply (IH (VTuple l)). reflexivity.

- unfold le. unfold Value_DefinedRelation.
  apply (le_list_gen_refl l (le_list_abstract_byte_refl)).
Qed.

Lemma le_option_val_refl (o: option Value) : le o o.
Proof.
apply le_option_gen_refl.
apply le_val_refl.
Qed.

Lemma le_list_step {x1 x2 : AbstractByte} {l1 l2} : le (x1 :: l1) (x2 :: l2) = (le x1 x2 /\ le l1 l2).
Proof.
auto.
Qed.
