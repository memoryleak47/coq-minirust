From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils subslice le.
Require Import List Nat PeanoNat Bool Lia ssreflect.
Import ListNotations.

Section tuple.

Context {params: Params}.
Context {fields: Fields}.
Context {size: Size}.

Notation t := (TTuple fields size).
Context (props_IH : Forall (fun ty : Ty => wf ty -> Props ty) (map snd fields)).
Context (Hwf: wf t).

Lemma fields_fit_size_l : fields_fit_size fields size.
apply Hwf.
Qed.

Lemma props_fields : Forall Props (map snd fields).
Proof.
assert (Forall wf (map snd fields)). {
  inversion Hwf as (_ & _ & H & _).
  clear Hwf.
  induction fields. { apply Forall_nil. }
  simpl.
  destruct a as [_left x].
  simpl in H.
  apply Forall_cons.
  { inversion H. auto. }

  apply IHf.
  { simpl in props_IH. inversion props_IH. auto. }
  { inversion H. auto. }
}

clear Hwf.
induction fields. { apply Forall_nil. }

apply Forall_cons.
{ inversion props_IH. apply H2. inversion H. auto. }

apply IHf.
{ inversion props_IH. auto. }
{ inversion H. auto. }
Qed.

Lemma dec_to_enc {vals l} a
(Hl: length l = size)
(Ha: length a = size)
(H : transpose (map (decode_tuple_field decode l) fields) = Some vals)
: exists l', encode_tuple_fields a fields encode vals = Some l'.
Proof.
pose proof props_fields as Hprops.
pose proof fields_fit_size_l as Hfit.

clear Hwf.
clear props_IH.

generalize dependent fields.
generalize dependent a.

induction vals as [|v vals IH]. {
  intros. destruct fields0. { simpl. eexists _. auto. }
  pose proof transpose_len H.
  rewrite map_length in H0.
  discriminate H0.
}

intros a Ha fs H Hprops Hfit.
destruct fs as [|[off ty] fs].
{ pose proof transpose_len H. discriminate H0. }

simpl.

assert (exists ll, decode ty ll = Some v). {
  simpl in H.
  set D := (subslice_with_length _ _ _) in H.
  destruct (decode ty D) eqn:E; cycle 1. { discriminate H. }
  set tr := transpose _ in H.
  destruct tr; cycle 1. { simpl in H. discriminate H. }
  simpl in H.
  exists D.
  rewrite E.
  inversion H. auto.
}

assert (Props ty). { inversion Hprops. auto. }

destruct (PR_RT1 _ H1 v H0) as (ll & Henc & _).
rewrite Henc.
simpl.

set a' := (write_subslice_at_index _ _ _).
refine (IH a' _ fs _ _ _ ).
{ apply write_subslice_length. auto.
{ inversion Hfit.
  simpl in H4.
  rewrite Ha.
  rewrite (PR_ENCODE_LEN _ H1 v ll Henc).
  auto.
}
}
{ simpl in H.
  destruct (decode ty (subslice_with_length l off (ty_size ty))); cycle 1. { discriminate H. }
  destruct (transpose (map (decode_tuple_field decode l) fs)); cycle 1. { discriminate H. }
  inversion H.
  auto.
}
{ inversion Hprops. auto. }
{ inversion Hfit. auto. }
Qed.

Lemma tuple_dec [l v] (H: decode t l = Some v) :
  length l = size /\
  exists vals,
  transpose (map (decode_tuple_field decode l) fields) = Some vals /\
  v = VTuple vals /\
  exists l', encode t v = Some l'.
Proof.
unfold decode in H. fold decode in H. unfold decode_tuple in H.
set tr := transpose _ in H.
destruct tr as [vals|] eqn:Htr; cycle 1. { discriminate H. }

simpl in H.
destruct (Nat.eqb_spec (length l) size); cycle 1. { discriminate H. }

split. { auto. }
exists vals.
simpl in H. inversion H. clear H v H1.

set H1 := transpose _ = Some vals.
assert (H1). { auto. }
unfold H1 in *. clear H1.

split; auto.
split; auto.

unfold encode. fold encode. unfold encode_tuple.

unfold assuming.
simpl.

assert (length vals = length fields). {
  rewrite <- (transpose_len H).
  apply map_length.
}

destruct (Nat.eqb_spec (length vals) (length fields)); cycle 1. { lia. }

simpl.

refine (dec_to_enc _ e _ H).
apply repeat_length.
Qed.

Lemma tuple_rt1 : rt1 t.
intros v [l Hdec].
destruct (tuple_dec Hdec) as (Hlen & vals & Htr & -> & l' & Henc).
exists l'.
split. { auto. }
Admitted.

Lemma tuple_rt2 : rt2 t.
Admitted.

Lemma tuple_mono1 : mono1 t.
Admitted.

Lemma tuple_mono2 : mono2 t.
Admitted.

Lemma tuple_encode_len : encode_len t.
Admitted.

Lemma tuple_props : Props t.
Proof.
split.
- auto.
- apply tuple_rt1.
- apply tuple_rt2.
- apply tuple_mono1.
- apply tuple_mono2.
- apply tuple_encode_len.
Qed.

End tuple.
