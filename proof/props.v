From Minirust.def Require Import ty encoding thm wf.
From Minirust.proof Require Import defs int bool ptr array union tuple ty_ind.
Require Import List.
Import ListNotations.

Section props.

Context {params: Params}.

Lemma gen_props (ty: Ty) : wf ty -> Props ty.
Proof.
induction ty using ty_ind; intros Hwf.
- apply (bool_props Hwf).
- apply (int_props Hwf).
- apply (ptr_props Hwf).
- apply (tuple_props H Hwf).
- apply (array_props IHty Hwf).
- apply (union_props Hwf).
Qed.

Theorem gen_rt1 (ty: Ty) : wf ty -> rt1 ty.
Proof. intros Hwf. destruct (gen_props ty); auto. Qed.

Theorem gen_rt2 (ty: Ty) : wf ty -> rt2 ty.
Proof. intros Hwf. destruct (gen_props ty); auto. Qed.

Theorem gen_mono1 (ty: Ty) : wf ty -> mono1 ty.
Proof. intros Hwf. destruct (gen_props ty); auto. Qed.

Theorem gen_mono2 (ty: Ty) : wf ty -> mono2 ty.
Proof. intros Hwf. destruct (gen_props ty); auto. Qed.

End props.
