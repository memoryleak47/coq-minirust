Require Import Lia List.
Import ListNotations.
From Minirust.def Require Import ty encoding le.
From Minirust.proof.lemma Require Import le wrap_abstract.

Section unique_prov.

Context {memory: Memory}.

Lemma unique_prov_cons2 {a} {b} {l} {p} (H: unique_prov (a :: b :: l) = Some p) :
  unique_prov (b :: l) = Some p.
Proof.

destruct a.
{ discriminate H. }

destruct o; cycle 1.
{ discriminate H. }

destruct b.
{ unfold unique_prov in H. simpl in H. destruct (P_EQ_REFLECT p0 p0); auto. }

destruct o; cycle 1.
{ unfold unique_prov in H. simpl in H. destruct (P_EQ_REFLECT p0 p0); auto. }

destruct (P_EQ_REFLECT p0 p1).
- unfold unique_prov in H.
  simpl in H.
  destruct (P_EQ_REFLECT p0 p0); cycle 1.
  { exfalso. apply n. auto. }

  destruct (P_EQ_REFLECT p1 p0); cycle 1.
  { simpl in H. discriminate H. }

  simpl in H.
  unfold unique_prov.
  rewrite <- H.
  simpl.
  f_equal; try auto.

  destruct (P_EQ_REFLECT p1 p1); cycle 1.
  { exfalso. apply n. auto. }

  simpl.
  rewrite <- e.
  auto.
- unfold unique_prov in H.
  simpl in H.

  destruct (P_EQ_REFLECT p0 p0); cycle 1.
  { exfalso. apply n0. auto. }

  destruct (P_EQ_REFLECT p1 p0); cycle 1.
  { simpl in H. discriminate H. }

  simpl in H.
  exfalso.
  apply n.
  auto.
Qed.

Lemma unique_le {l1 l2: list AbstractByte} (Hle: le l1 l2) p (H: unique_prov l1 = Some p) :
  unique_prov l2 = Some p.
Proof.
assert (l1 = l2); cycle 1.
{ rewrite <- H0. auto. }

induction (mk_le_list _ _ Hle) as [| ab1 ab2 l1 l2 HLe IH HLeAB _].
{ auto. }

assert (le l1 l2) as Hle'.
{ simpl in Hle. inversion Hle. assumption. }

assert (ab1 = ab2). {
  destruct ab1.
  { unfold unique_prov in H. simpl in H. discriminate H. }

  destruct HLeAB.
  - unfold unique_prov in H. discriminate H.
  - unfold unique_prov in H. discriminate H.
  - simpl in Hle. inversion Hle. inversion H0; auto.
}
rewrite <- H0. rewrite <- H0 in Hle,HLeAB. clear H0 ab2.
f_equal.

destruct l1.
- destruct l2.
-- auto.
-- contradiction Hle'.
- apply IH.
-- assumption.
-- apply (unique_prov_cons2 H).
Qed.

Lemma unique_prov_dev {b} {p} {b0} {l} : unique_prov (Init b p :: Init b0 p :: l) = unique_prov (Init b0 p :: l).
Proof.
unfold unique_prov.
simpl.
destruct p.
- simpl.
  destruct (P_EQ_REFLECT p p); auto.
- simpl. auto.
Qed.

Lemma unique_wrap {l} {p} (H: length l > 0): unique_prov (wrap_abstract l p) = p.
Proof.
induction l as [|b l IH].
- simpl in H.
  assert (~(0 > 0)). { lia. }
  exfalso.
  apply H0.
  assumption.
- destruct l.
-- unfold unique_prov.
   simpl.
   destruct p.
--- simpl.
    destruct (P_EQ_REFLECT p p); auto.
    contradict n.
    auto.
--- simpl. auto.
-- simpl.
   simpl in IH.
   rewrite unique_prov_dev.
   apply IH.
   lia.
Qed.

Lemma wrap_unique_le {bl l} (H: unwrap_abstract l = Some bl) : le (wrap_abstract bl (unique_prov l)) l.
Proof.
destruct (unique_prov l) eqn:Huniq; cycle 1.
{ apply unwrap_le; assumption. }

assert (wrap_abstract bl (Some p) = l); cycle 1.
{ rewrite H0. apply (le_list_abstract_byte_refl l). }

generalize dependent bl.
induction l as [|ab l IH].
{ unfold unique_prov in Huniq. simpl in Huniq. discriminate Huniq. }

intros bl H.
destruct bl. {
  destruct ab.
  - simpl in H. discriminate H.
  - simpl in H. destruct (unwrap_abstract l); simpl in H; discriminate H.
}

simpl.
assert (Init b (Some p) = ab) as Hab. {
  destruct ab.
  { simpl in H. discriminate H. }

  assert (b = b0). {
    simpl in H.
    destruct (unwrap_abstract l).
    - simpl in H. inversion H. auto.
    - simpl in H. discriminate H.
  }

  rewrite H0.
  f_equal.

  unfold unique_prov in Huniq.
  destruct o; cycle 1.
  { simpl in Huniq. discriminate Huniq. }

  simpl in Huniq.
  destruct ((P_EQ p0 p0 &&
           forallb
             (fun x : AbstractByte =>
              match x with
              | Init _ (Some a) =>
                  P_EQ a p0
              | _ => false
              end) l))%bool eqn:E.
  - simpl in Huniq. inversion Huniq. auto.
  - simpl in Huniq. discriminate Huniq.
}

rewrite Hab.
f_equal.

destruct l eqn:E. {
  destruct ab.
  { simpl in Hab. discriminate Hab. }

  simpl in H. inversion H.
  simpl. auto.
}

apply IH.
- apply (unique_prov_cons2 Huniq).
- simpl in H.
  destruct ab. { discriminate H. }
-- destruct a.
   { simpl in H. discriminate H. }

   simpl in H. inversion H.
   simpl.
   destruct (unwrap_abstract l0).
--- simpl. simpl in H. inversion H. auto.
--- simpl in H. discriminate H.
Qed.

End unique_prov.