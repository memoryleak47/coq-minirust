Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Lemma ptr_mono1 (ptr_ty: PtrTy) : mono1 (TPtr ptr_ty).
Proof.
Admitted.

Lemma ptr_mono2 (ptr_ty: PtrTy) : mono2 (TPtr ptr_ty).
Proof.
Admitted.

Lemma ptr_rt1 (ptr_ty: PtrTy) : rt1 (TPtr ptr_ty).
Proof.
Admitted.

Lemma int_rt2 (ptr_ty: PtrTy) : rt2 (TPtr ptr_ty).
Proof.
Admitted.