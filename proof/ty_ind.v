Require Import List Lia Nat PeanoNat ssreflect.
From Minirust Require Import ty.

Fixpoint ty_depth (t: Ty) : nat :=
  match t with
  | TBool => 0
  | TInt _ _ => 0
  | TPtr _ _ => 0
  | TTuple fields _size => S (list_max (map (fun x => ty_depth (snd x)) fields))
  | TArray sub_ty _count => S (ty_depth sub_ty)
  | TUnion fields _chunks _size => S (list_max (map (fun x => ty_depth (snd x)) fields))
  end.

Lemma ty_ind
  (P : Ty -> Prop)
  (HBool : P TBool)
  (HInt : forall size signedness, P (TInt size signedness))
  (HPtr : forall ptr_ty layout, P (TPtr ptr_ty layout))
  (HTuple : forall fields size, Forall P (map snd fields) -> P (TTuple fields size))
  (HArray : forall sub_ty count, P sub_ty -> P (TArray sub_ty count))
  (HUnion : forall fields chunks size, Forall P (map snd fields) -> P (TUnion fields chunks size))
  : forall t, P t.
Proof.
assert (forall n, forall m, m <= n -> forall t, ty_depth t = m -> P t); cycle 1.
{ intros. apply (H (ty_depth t) (ty_depth t)); auto. }

intros n.
induction n as [|n IH]. {
  intros.
  destruct m; try lia.
  destruct t; try discriminate H0; auto.
}

intros.
destruct (Nat.ltb_spec m (S n)).
{ destruct m as [|m].
  - apply (IH 0); auto; lia.
  - assert (m < n). { lia. }
    apply (IH (S m)); auto.
}

assert (m = S n) as ->. { lia. }
clear H1 H.

destruct t; try discriminate H0.
(* tuples *)
{
  apply HTuple.
  simpl in H0. inversion H0. clear H0.
  apply (proj2 (Forall_map _ _ _)).
  set ll := map _ l in H1.
  assert (list_max ll <= n). { lia. }
  pose proof proj1 (list_max_le _ _) H.
  unfold ll in H0.
  pose proof proj1 (Forall_map _ _ _) H0.
  refine (Forall_impl _ _ H2).
  intros [_left x] Ha.
  simpl (snd _) in *.
  apply (IH (ty_depth x)); lia.
}

(* arrays *)
{
  apply HArray.
  apply (IH (ty_depth t)); try lia.
  simpl in H0.
  lia.
}

(* unions *)
{
  apply HUnion.
  simpl in H0. inversion H0. clear H0.
  apply (proj2 (Forall_map _ _ _)).
  set ll := map _ l in H1.
  assert (list_max ll <= n). { lia. }
  pose proof proj1 (list_max_le _ _) H.
  unfold ll in H0.
  pose proof proj1 (Forall_map _ _ _) H0.
  refine (Forall_impl _ _ H2).
  intros [_left x] Ha.
  simpl (snd _) in *.
  apply (IH (ty_depth x)); lia.
}
Qed.
