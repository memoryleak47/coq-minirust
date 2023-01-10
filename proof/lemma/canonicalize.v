Require Import Lia Coq.Init.Byte FunctionalExtensionality NArith ZArith List Ndigits NArith ssrbool.
Import ListNotations.

From Minirust.def Require Import ty encoding thm utils wf.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils.

Section canonicalize.

Context [ty: Ty].
Context (ty_props: Props ty).

Lemma canonicalize_lemma1 {l: list AbstractByte} (H: exists v, decode ty l = Some v) :
  exists l', canonicalize ty l = Some l'.
Proof.
destruct H as [v H].
assert (Hval: is_valid_for ty v).
{ exists l. auto. }

destruct (PR_RT1 ty ty_props v Hval) as [l' [Henc Hdec]].
unfold canonicalize.
rewrite H.
simpl.
exists l'.
assumption.
Qed.

Lemma canonicalize_lemma2 {ls vs} (H: transpose (map (decode ty) ls) = Some vs) :
  exists ll, transpose (map (canonicalize ty) ls) = Some ll.
Proof.
generalize dependent vs.
induction ls as [|x ll IH].
{ intros vs X. simpl in X. inversion X. exists []. auto. }

intros vs X.
simpl.
destruct (decode ty x) as [v|] eqn:Hdec; cycle 1.
{ simpl in X. rewrite Hdec in X. simpl in X. discriminate X. }

assert (Hv: exists v, decode ty x = Some v).
{ exists v. auto. }

destruct (canonicalize_lemma1 Hv) as [x' Hx'].
rewrite Hx'.

simpl in X.
rewrite Hdec in X.


destruct (transpose (map (decode ty) ll)) eqn:E; cycle 1.
{ simpl in X. discriminate X. }

destruct (IH l eq_refl).
rewrite H.
simpl.
exists (x' :: x0).
auto.
Qed.

Lemma canonicalize_len {l l'} (H: canonicalize ty l = Some l') :
  length l' = ty_size ty.
Proof.
unfold canonicalize in H.
destruct (decode ty l) eqn:E; cycle 1.
{ simpl in H. discriminate H. }

simpl in H.
apply (PR_ENCODE_LEN ty ty_props v l' H).
Qed.

End canonicalize.
