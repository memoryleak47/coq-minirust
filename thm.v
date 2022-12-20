Require Import defs.
Require Import le.
Require Import lemma.

Require Import Coq.Bool.Bool.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Import ListNotations.

Theorem mono1 (ty: Ty) (v1 v2: Value) (p: le_val v1 v2) (p1: is_valid_for ty v1) (p2: is_valid_for ty v2) :
exists e1, exists e2, encode ty v1 = Some e1 /\ encode ty v2 = Some e2 /\ le_list e1 e2.
Proof.
(*
destruct v1,v2.
unfold le_val in p.
simpl in p.
replace b0 with b.
apply obvious.
Qed.
*)
Abort.

Theorem mono2 (ty: Ty) (l1 l2: list AbstractByte) (p: le_list l1 l2) : le_opt (decode ty l1) (decode ty l2).
Proof.
(*
destruct ty.
destruct (mk_le_list l1 l2 p) as [|x1 x2 l1' l2' p' H].
- unfold le_opt,decode. assumption.
- destruct p'; clear p.
  destruct H.
-- unfold le_opt,decode. auto.
-- unfold decode. destruct x; unfold le_opt; try auto.
--- unfold le_val. reflexivity.
--- unfold le_val. reflexivity.
-- unfold decode. destruct x; unfold le_opt; try auto.
--- unfold le_val. reflexivity.
--- unfold le_val. reflexivity.
-- unfold decode.
destruct x1; destruct x2; try destruct b; unfold le_opt; auto.
Qed.
*)
Abort.

Theorem roundtrip1 (ty: Ty) (v: Value) (p: is_valid_for ty v) :
exists e, encode ty v = Some e /\ decode ty e = Some v.
Proof.
(*
destruct ty.
destruct v.
destruct b; unfold encode,decode; reflexivity.
Qed.
*)
Abort.

Theorem roundtrip2 (ty: Ty) (l: list AbstractByte) (v: Value) (H: decode ty l = Some v) :
exists e, encode ty v = Some e /\ le_list e l.
Proof.
(*
destruct ty.
destruct v.
destruct (mk_decode_bool l).
- unfold decode in H. inversion H.
  unfold encode. unfold le_list. split; try auto.
  unfold le_abstract_byte. reflexivity.
- unfold decode in H. inversion H.
  unfold encode. unfold le_list. split; try auto.
  unfold le_abstract_byte. reflexivity.
- rewrite e in H. discriminate H.
Qed.
*)
Abort.
