Require Import List Lia FunctionalExtensionality.
Import ListNotations.
From Minirust.def Require Import encoding utils.
From Minirust.proof.lemma Require Import utils subslice.

Lemma chunks_step {s c T} {l: list T}: chunks (S c) s l = (firstn s l)::(chunks c s (skipn s l)).
Proof.
unfold chunks.
simpl.
rewrite subslice_zero.
f_equal.
unfold subslice_with_length.
rewrite <- seq_shift.
rewrite map_map.
f_equal.
apply functional_extensionality_dep.
intros x.
f_equal.
rewrite skipn_add.
f_equal.
lia.
Qed.

Lemma concat_len {T n k} {ll: list (list T)}
  (Hl1: length ll = k)
  (Hl2: Forall (fun x => length x = n) ll) :
  length (concat ll) = n * k.
Proof.
generalize dependent ll.
generalize dependent n.
induction k as [|k]. {
  intros.
  rewrite ((proj1 (length_zero_iff_nil ll)) Hl1).
  simpl.
  lia.
}

intros n ll Hlen Hlen_inner.

destruct ll.
{ inversion Hlen. }

assert (length ll = k).
{  inversion Hlen. auto. }

assert (length l = n).
{ inversion Hlen_inner. auto. }

assert (length (concat ll) = n * k). {
  apply IHk. { assumption. }

  inversion Hlen_inner.
  auto.
}

simpl.
rewrite app_length.
lia.
Qed.

Lemma chunks_len1 {T c s} {l: list T} (H: length l = c * s) :
  length (chunks c s l) = c.
Proof.
generalize dependent l.
induction c.
{ intros l H. simpl. auto. }

intros l H.
simpl.
f_equal.
rewrite map_length.
apply seq_length.
Qed.

Lemma chunks_len2 {T c s} {l: list T} (H: length l = c * s) :
  Forall (fun x => length x = s) (chunks c s l).
Proof.
generalize dependent l.
induction c as [|c IH].
{ intros l H. apply Forall_nil. }

intros l H.
rewrite chunks_step.
apply Forall_cons.
{ rewrite firstn_length. lia. }

apply IH.
rewrite skipn_length.
lia.
Qed.

Lemma chunks_len {T c s} {l: list T} (H: length l = c * s) :
  length (chunks c s l) = c /\ Forall (fun x => length x = s) (chunks c s l).
Proof. split; [> apply (chunks_len1 H) | apply (chunks_len2 H)]. Qed.

Lemma chunks_concat {T c s} {l : list (list T)} (H1: length l = c) (H: Forall (fun x => length x = s) l) :
  chunks c s (concat l) = l.
Proof.
Admitted.
