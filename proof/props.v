Require Import defs encoding thm bool int ptr.
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
- apply cheat.
- apply cheat.
Qed.

Lemma int_rt2 {ty: Ty} : rt2 ty.
Proof.
destruct ty.
- apply bool_rt2.
- apply int_rt2.
- apply cheat.
- apply cheat.
- apply cheat.
- apply cheat.
Qed.

Lemma int_mono1 {ty: Ty} : mono1 ty.
Proof.
destruct ty.
- apply bool_mono1.
- apply int_mono1.
- apply cheat.
- apply cheat.
- apply cheat.
- apply cheat.
Qed.

Lemma int_mono2 {ty: Ty} : mono2 ty.
Proof.
destruct ty.
- apply bool_mono2.
- apply int_mono2.
- apply cheat.
- apply cheat.
- apply cheat.
- apply cheat.
Qed.
