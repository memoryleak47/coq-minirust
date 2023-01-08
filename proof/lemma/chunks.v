Require Import List Lia.
Import ListNotations.
From Minirust.def Require Import utils.
From Minirust.proof.lemma Require Import utils.

Notation cstep l s := (
  match firstn s l with
  | [] => []
  | x => x::(chunks (skipn s l) s)
  end
).

Lemma skipn_smaller {T s} {l: list T} : length l >= length (skipn s l).
Proof.
generalize dependent s.
induction l as [|x l IH].
{ intros. destruct s; simpl; lia. }

intros.
simpl.
destruct s. { simpl. lia. }
simpl.
have H (IH s).
lia.
Qed.

Lemma waste_extra_gas {T s g1 g2} {l: list T} (H1: g1 >= length l) (H2: g2 >= length l):
  chunks_impl g1 l (S s) = chunks_impl g2 l (S s).
Proof.
generalize dependent g2.
generalize dependent l.

induction g1 as [|g1 IH].
{ intros. destruct l; try simpl in H1; try lia; destruct g2; simpl; auto. }

intros.
destruct l.
{ simpl. destruct g2; simpl; auto. }

destruct g2.
{ simpl in H2. lia. }

simpl.
f_equal.
assert (length (skipn s l) <= length l). { apply skipn_smaller. }

assert (g1 >= length l).
{ simpl in H1. lia. }

assert (g2 >= length l).
{ simpl in H2. lia. }

apply IH; lia.
Qed.

Lemma chunks_step {T s} {l: list T} : chunks l s = cstep l s.
Proof.
(* first, finish the s = 0 case, where no iteration happens at all *)
destruct s.
{ unfold chunks. simpl. destruct l; simpl; auto. }

unfold chunks.

induction l as [| x l IH].
{ unfold chunks. auto. }

simpl.
f_equal.
refine (waste_extra_gas _ _).
- apply skipn_smaller.
- lia.
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

Lemma chunks_len {T n k} {l: list T} (H: length l = n * k) :
  length (chunks l n) = k /\ Forall (fun x => length x = n) (chunks l n).
Proof.
Admitted.


Lemma chunks_concat {T} {s} {l : list (list T)} (H: Forall (fun x => length x = s) l) :
  chunks (concat l) s = l.
Proof.
Admitted.