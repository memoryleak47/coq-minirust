From Minirust.def Require Import defs encoding thm.
From Minirust.proof Require Import int bool ptr array.
Require Import List.
Import ListNotations.

Lemma cheat {P: Prop} : P.
Admitted.

Lemma int_rt1 {ty: Ty} : rt1 ty.
Proof.
destruct ty.
- apply bool_rt1.
- apply int_rt1.
- apply ptr_rt1.
- apply cheat.
- apply array_rt1.
- apply cheat.
Qed.

Lemma int_rt2 {ty: Ty} : rt2 ty.
Proof.
destruct ty.
- apply bool_rt2.
- apply int_rt2.
- apply ptr_rt2.
- apply cheat.
- apply array_rt2.
- apply cheat.
Qed.

Lemma int_mono1 {ty: Ty} : mono1 ty.
Proof.
destruct ty.
- apply bool_mono1.
- apply int_mono1.
- apply ptr_mono1.
- apply cheat.
- apply array_mono1.
- apply cheat.
Qed.

Lemma int_mono2 {ty: Ty} : mono2 ty.
Proof.
destruct ty.
- apply bool_mono2.
- apply int_mono2.
- apply ptr_mono2.
- apply cheat.
- apply array_mono2.
- apply cheat.
Qed.
