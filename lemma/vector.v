Require Import Coq.Init.Byte FunctionalExtensionality EqdepFacts List Ndigits ZArith Zpow_facts Lia.

Lemma vector_retype {T O: Type} {n: nat} (f: forall n, Vector.t T n -> O) (v: Vector.t T n) (m:nat) :
  forall (P: n=m), f n v = f m (eq_rect n (Vector.t T) v m P).
Proof.
intros P.
rewrite <- P.
rewrite <- Eqdep_dec.eq_rect_eq_dec.
reflexivity.
apply PeanoNat.Nat.eq_dec.
Qed.

Lemma of_list_to_list {T O: Type} {n:nat} (v:Vector.t T n) (f : forall n, Vector.t T n -> O) :
  f _ (Vector.of_list (Vector.to_list v)) = f n v.
Proof.
rewrite (vector_retype f _ n (Vector.length_to_list _ _ _)).
rewrite Vector.of_list_to_list_opp.
reflexivity.
Qed.

Lemma rewrite_empty_vector {T: Type} (v: Vector.t T 0) : v = Vector.nil T.
Proof.
apply (@Vector.case0 T (fun v => v = Vector.nil T)).
reflexivity.
Qed.

Lemma rewrite_non_empty_vector {T:Type} {n: nat} (v: Vector.t T (S n)) :
  exists h t, v = Vector.cons T h n t.
Proof.
induction n,v using Vector.caseS.
- exists h, v. reflexivity.
Qed.
