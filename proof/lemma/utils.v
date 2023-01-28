Require Import List Lia Nat Bool.
Import ListNotations.
From Minirust.def Require Import utils ty le.
From Minirust.proof.lemma Require Import le.

Lemma declare_impl {T: Type} (t: T) : exists t', t=t'. exists t. reflexivity. Qed.

Ltac declare x Hx obj := destruct (declare_impl obj) as [x Hx].
Ltac have x obj := destruct (declare_impl obj) as [x _].

Definition contains i (interval: nat * nat) := (
  (fst interval <=? i) &&
  (i <? fst interval + snd interval)
).

Lemma bind_some {T T'} {x: T} {f: T -> option T'} : (Some x >>= f) = f x.
Proof.
simpl. auto.
Qed.

Lemma bind_none {T T'} {f: T -> option T'} : (None >>= f) = None.
Proof.
simpl. auto.
Qed.

Lemma transpose_map {T1 T2 T3} {f: T1 -> option T2} {g: T2 -> option T3} {l: list T1} {l'} (H: transpose (map f l) = Some l') :
map g l' = map (fun x => (f x) >>= g) l.
Proof.
generalize dependent l'.
induction l as [|x l IH].
{ intros l' H. simpl in H. inversion H. simpl. auto. }

intros l' H.
simpl in H.
destruct (f x) as [t2|] eqn:Hfx; cycle 1.
{ discriminate H. }

destruct (transpose (map f l)) as [l2|] eqn:E; cycle 1.
{ simpl in H. discriminate H. }

simpl in H.
inversion H.
simpl.
rewrite Hfx.
simpl.
f_equal.
apply IH.
auto.
Qed.

Lemma transpose_some {T} {x: T} {l: list (option T)} : transpose ((Some x) :: l) = (transpose l o-> (fun a => x :: a)).
Proof. simpl. auto. Qed.

Lemma transpose_len {T r} {l: list (option T)} (H: transpose l = Some r) :
  length l = length r.
Proof.
generalize dependent r.
induction l.
{ intros r X. inversion X. auto. }

intros r X.
simpl.
destruct r.
{ destruct a; inversion X; destruct (transpose l); simpl in H0; discriminate H0. }
simpl.
f_equal.
apply IHl.
inversion X.
destruct a; destruct (transpose l); inversion H0; auto.
Qed.

Lemma transpose_nil {T1 T2 l} {f: T1 -> option T2} (H: transpose (map f l) = Some []) :
 l = [].
Proof.
destruct l. { auto. }
simpl in H.
destruct (f t); cycle 1.
{ discriminate H. }

destruct (transpose (map f l)); cycle 1.
{ simpl in H. discriminate H. }

simpl in H.
inversion H.
Qed.

Lemma transpose_map_Forall {T1 T2} {l: list T1} {l': list T2} {P: T2 -> Prop} {f: T1 -> option T2}
  (A: transpose (map f l) = Some l')
  (B: forall x, forall y, f x = Some y -> P y) :
  Forall P l'.
Proof.
generalize dependent l'.
induction l as [|x l IH].
{ intros l' A. simpl in A. inversion A. apply Forall_nil. }

intros l' A.
destruct l'.
{ destruct (transpose_nil A). auto. }

simpl in A.

destruct (f x) eqn:F; cycle 1.
{ discriminate A. }

destruct (transpose (map f l)) eqn:G; cycle 1.
{ discriminate A. }

simpl in A.
inversion A.
rewrite <- H0.
apply Forall_cons.
- apply (B _ _ F).
- apply IH. inversion H1. auto.
Qed.

Section utils.

Context {params:Params}.

Lemma transpose_le_step [o1 o2: option (list Value)] [v1 v2]
  (Hle1: le o1 o2)
  (Hle2: le v1 v2) :
  le (o1 o-> (fun r => v1 :: r)) (o2 o-> (fun r => v2 :: r)).
Proof.
destruct o1; cycle 1.
{ simpl. auto. }

destruct o2; cycle 1.
{ simpl. auto. }

simpl (Some _ o-> _).
assert (le (v1 :: l) (v2 :: l0)); cycle 1. { auto. }

rewrite le_list_step.
auto.
Qed.

Lemma transpose_le [l1 l2: list (option Value)] (Hle: le l1 l2) :
  le (transpose l1) (transpose l2).
Proof.
generalize dependent l2.
induction l1 as [|x1 l1 IH].
{ intros. simpl in Hle. destruct l2; auto. contradict Hle. }

intros.
destruct l2 as [|x2 l2].
{ contradict Hle. }

destruct x1; cycle 1.
{ simpl. auto. }

destruct x2; cycle 1.
{ simpl in Hle. contradict (proj1 Hle). }

simpl (transpose (Some _ :: _)).
assert (le l1 l2).
{ inversion Hle. auto. }

have A (IH l2 H).
apply (transpose_le_step A).
inversion Hle.
auto.
Qed.

Lemma map_nth_switchd {A B : Type} {f : A -> B}
                      (da: A) {l : list A} {n : nat} {db : B}
  (H: n < length l) :
  nth n (map f l) db = f (nth n l da).
Proof.
generalize dependent n.
induction l as [|x l IH].
{ intros. destruct n; simpl in H; lia. }

intros.
destruct n as [|n]. { auto. }

simpl.
apply IH.
simpl in H.
lia.
Qed.

Lemma transpose_nth_ext {T} {xs: list T} {l: list (option T)} (Hlen: length l = length xs) (H: forall def j, j < length l -> nth j l None = Some (nth j xs def))
 : transpose l = Some xs.
Proof.
Admitted.

Lemma transpose_nth {T xs} {l: list (option T)} (H: transpose l = Some xs) :
  forall def j, j < length l -> nth j l None = Some (nth j xs def).
Admitted.


End utils.