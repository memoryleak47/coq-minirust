From Minirust.def Require Import defs encoding thm.
From Minirust Require Import proofdefs.
From Minirust.proof Require Import int bool ptr array.
Require Import List.
Import ListNotations.

Lemma cheat {P: Prop} : P.
Admitted.

Lemma gen_props (ty: Ty) : Props ty.
Proof.
induction ty.
- apply bool_props.
- apply int_props.
- apply ptr_props.
- apply cheat.
- apply (array_props IHty).
- apply cheat.
Qed.

Theorem gen_rt1 (ty: Ty) : rt1 ty.
Proof. destruct (gen_props ty). assumption. Qed.

Theorem gen_rt2 (ty: Ty) : rt2 ty.
Proof. destruct (gen_props ty). assumption. Qed.

Theorem gen_mono1 (ty: Ty) : mono1 ty.
Proof. destruct (gen_props ty). assumption. Qed.

Theorem gen_mono2 (ty: Ty) : mono2 ty.
Proof. destruct (gen_props ty). assumption. Qed.