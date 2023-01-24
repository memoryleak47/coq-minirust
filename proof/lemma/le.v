From Minirust.def Require Import ty le.
Require Import Datatypes Coq.Init.Byte List Lia.
Import ListNotations.

Section le.

Context {params: Params}.

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
  destruct (P_EQ_REFLECT p p); auto.
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

Lemma le_list_step {T} {x1 x2 : T} {_: DefinedRelation T} {l1 l2} : le (x1 :: l1) (x2 :: l2) = (le x1 x2 /\ le l1 l2).
Proof.
auto.
Qed.

Lemma le_len [T] {l1 l2 : list T} {_: DefinedRelation T} (H: le l1 l2)
  : length l1 = length l2.
Proof.
generalize dependent l2.

induction l1 as [|x1 l1 IH].
{ intros. simpl in H. destruct l2; auto. contradict H. }

intros.
destruct l2.
{ contradict H. }

simpl.
f_equal.
apply IH.
inversion H.
auto.
Qed.

Lemma le_nth [T] {l1 l2 : list T} {_: DefinedRelation T}
  (default: T)
  (Hlen : length l1 = length l2)
  (H : forall i, i < length l1 -> le (nth i l1 default) (nth i l2 default)) :
le l1 l2.
Proof.
generalize dependent l2.
induction l1 as [|x1 l1 IH].
{ intros. destruct l2; try discriminate Hlen. simpl. auto. }

intros.
destruct l2 as [|x2 l2].
{ simpl in Hlen. discriminate Hlen. }

simpl.
split.
{ apply (H 0). simpl. lia. }

apply IH.
{ simpl in Hlen. inversion Hlen. auto. }

intros.
apply (H (S i)).
simpl. lia.
Qed.

Lemma le_nth_rev {T j} {l1 l2: list T} {_: DefinedRelation T}
  (default: T)
  {refl: forall (x: T), le x x}
  (H: le l1 l2)
  : le (nth j l1 default) (nth j l2 default).
Proof.
generalize dependent l2.
generalize dependent j.
induction l1 as [|x1 l1 IH].
{ intros. destruct l2; try contradiction H. apply refl. }

intros.
destruct l2 as [|x2 l2].
{ simpl in H. contradict H. }

destruct j.
{ inversion H. simpl. auto. }

simpl.
apply IH.
inversion H.
auto.
Qed.

End le.