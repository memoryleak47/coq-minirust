Require Import List.
Import ListNotations.
From Minirust.def Require Import utils.

Lemma declare_impl {T: Type} (t: T) : exists t', t=t'. exists t. reflexivity. Qed.

Ltac declare x Hx obj := destruct (declare_impl obj) as [x Hx].
Ltac have x obj := destruct (declare_impl obj) as [x _].

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