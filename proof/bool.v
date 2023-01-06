Require Import Coq.Init.Byte List.
Import ListNotations.

From Minirust.def Require Import defs encoding thm.
From Minirust.lemma Require Import le.

Inductive BoolCases1 : list AbstractByte -> Type :=
  | BC1True (p: option P) : BoolCases1 [Init x01 p]
  | BC1False (p: option P) : BoolCases1 [Init x00 p]
  | BC1Invalid (l: list AbstractByte) (H: decode TBool l = None) : BoolCases1 l.

Lemma mk_bool_cases1 (l: list AbstractByte) : BoolCases1 l.
Proof.
destruct l.
- apply BC1Invalid. auto.
- destruct l.
-- destruct a.
--- apply BC1Invalid. auto.
--- destruct b; try (apply BC1Invalid; reflexivity).
---- apply BC1False.
---- apply BC1True.
-- apply BC1Invalid. simpl.
   destruct a.
--- reflexivity.
--- destruct b; reflexivity.
Qed.

(* Lemma destruct_bool (v: Value) : is_valid_for TBool v -> exists b, v = VBool b. *)
Lemma valid_bool (v: Value) : is_valid_for TBool v -> exists b, v = VBool b.
Proof.
unfold is_valid_for.
unfold decode.
unfold decode_bool.
intros Hl.
destruct Hl as [l].
destruct (mk_bool_cases1 l).
- inversion H. exists true. reflexivity.
- inversion H. exists false. reflexivity.
- unfold decode in H0.
  unfold decode_bool in H0.
  rewrite H in H0. discriminate H0.
Qed.

Lemma bool_mono1 : mono1 TBool.
Proof.
unfold mono1.
intros _wf v1 v2 HLe valid1 valid2.
destruct (valid_bool v1 valid1) as [b1 H1].
destruct (valid_bool v2 valid2) as [b2 H2].
rewrite H1,H2 in HLe. simpl in HLe.
rewrite <- HLe in H2.
rewrite H1,H2.
destruct b1.
- do 2 exists [Init x01 None]. simpl. split; auto.
- do 2 exists [Init x00 None]. simpl. split; auto.
Qed.

Lemma bool_mono2 : mono2 TBool.
Proof.
unfold mono2.
intros _wf l1 l2 HLe.
destruct (mk_le_list _ _ HLe).
- auto.
- destruct l.
-- destruct l0.
--- simpl. auto.
--- destruct x; simpl; auto.
--- destruct x; simpl; auto.
-- unfold decode.
   unfold decode_bool.
   destruct b1;
   destruct b2;
   simpl;
   auto;
   destruct b;
   auto.
Qed.

Lemma bool_rt1 : rt1 TBool.
Proof.
unfold rt1.
intros _wf v valid.
destruct (valid_bool v valid) as [b H].
rewrite H. clear H valid v.
destruct b.
- exists [Init x01 None]. auto.
- exists [Init x00 None]. auto.
Qed.

Lemma bool_rt2 : rt2 TBool.
Proof.
unfold rt2.
intros _wf l v H.
destruct (mk_bool_cases1 l).
- inversion H. clear v H H1.
  exists [Init x01 None]. simpl. split; reflexivity || auto.
- inversion H. clear v H H1.
  exists [Init x00 None]. simpl. split; reflexivity || auto.
- rewrite H in H0. discriminate H0.
Qed.
