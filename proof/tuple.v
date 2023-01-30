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

(* the `i < size` argument is not really required here. It's only for historical reasons *)
Lemma fields_disjoint_l : forall i j1 j2, i < size -> j1 < length fields -> j2 < length fields -> j1 <> j2 ->
contains i (interval_of_field (nth j1 fields (0,TBool))) = true ->
contains i (interval_of_field (nth j2 fields (0, TBool))) = false.
Proof.
intros.
inversion Hwf.
inversion H5.
inversion H7.
apply (H9 i j1 j2); auto.
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
: exists l', encode_tuple_fields a fields encode vals = Some l' /\ length l' = size.
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
  exists l', encode t v = Some l' /\ length l' = size.
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

Lemma tuple_encode_len : encode_len t.
Proof.
intros v l Henc.
unfold encode in Henc. fold encode in Henc. unfold encode_tuple in Henc.
destruct v as [| | |vals|]; try discriminate Henc.
simpl in Henc.
unfold assuming in Henc.
destruct (length vals =? length fields); try discriminate Henc.
simpl in Henc.

(* note that we cannot prove `length vals = length fields` *)
(* it's not a problem though, encode_tuple_fields terminates when one of the lists is empty *)

assert (forall a, length a = size -> forall ll, encode_tuple_fields a fields encode vals = Some ll -> length ll = size); cycle 1. {
  simpl.
  refine (H (repeat Uninit size) _ l Henc).
  apply repeat_length.
}

pose proof fields_fit_size_l as Hfit.
pose proof props_fields as Hprops.
clear props_IH Hwf Henc.
generalize dependent vals.

induction fields as [|[off sub_ty] fs IH].
{ intros. simpl in H0. inversion H0. rewrite <- H2. auto. }

intros.
destruct vals as [|v vals].
{ simpl in H0. inversion H0. rewrite <- H2. auto. }

simpl in H0.
destruct (encode sub_ty v) eqn:E; cycle 1.
{ simpl in H0. discriminate H0. }

simpl in H0.
refine (IH _ _ vals (write_subslice_at_index a off l0) _ _ _); auto.
{ inversion Hfit. auto. }
{ inversion Hprops. auto. }
apply write_subslice_length; auto.
inversion Hfit.
simpl in H3.
rewrite H.
inversion Hprops.
rewrite (PR_ENCODE_LEN _ H7 _ _ E).
auto.
Qed.

Lemma encode_nth_some {l off sub_ty j vals} def
  (Hj : j < length fields)
  (Hvals_len : length vals = length fields)
  (Hfieldsj : nth j fields (0, TBool) = (off, sub_ty))
  (H : encode_tuple_fields (repeat Uninit size) fields encode vals = Some l)
: exists subl, encode sub_ty (nth j vals def) = Some subl.
Proof.
pose proof (repeat_length Uninit size) as Ha.
pose proof props_fields as Hprops.
pose proof fields_fit_size_l as Hfit.

clear props_IH Hwf.

generalize dependent (repeat Uninit size).
generalize dependent vals.
generalize dependent j.
induction fields as [|[off' sub_ty'] fs IH].
{ simpl in *. lia. }

intros.
destruct vals as [|v vals].
{ simpl in *. lia. }

destruct j as [|j]. {
  simpl in *.
  destruct (encode sub_ty' v) eqn:E; try discriminate.
  simpl in H.
  exists l1.
  inversion Hfieldsj.
  rewrite <- H2.
  auto.
}

simpl.
simpl in H.
destruct (encode sub_ty' v) eqn:E; try discriminate.
simpl in H.
refine (IH _ _ j _ _ vals _ _ H _); auto.
{ inversion Hprops. auto. }
{ inversion Hfit. auto. }
{ simpl in *. lia. }

apply write_subslice_length. { auto. }
rewrite Ha.
assert (length l1 = ty_size sub_ty') as ->. {
  inversion Hprops.
  apply (PR_ENCODE_LEN _ H2 _ _ E).
}
inversion Hfit.
simpl in H2.
auto.
Qed.

Lemma encode_nth_rest {fs i vals a r l}
  (Hfit: fields_fit_size fs size)
  (Hprops: Forall Props (map snd fs))
  (H : existsb (contains i) (map interval_of_field fs) = false)
  (Hi: i < size)
  (Ha_len : length a = size)
  (Hlens : length vals = length fs)
  (Hr: nth i a Uninit = r)
  (Henc: encode_tuple_fields a fs encode vals = Some l)
: nth i l Uninit = r.
Proof.
clear props_IH Hwf.

generalize dependent vals.
generalize dependent a.

induction fs as [|[off sub_ty] fs IH].
{ intros. simpl in Henc. inversion Henc. rewrite <- H1. auto. }

intros.
destruct vals as [|v vals].
{ simpl in *. discriminate. }

simpl in Henc.
destruct (encode sub_ty v) eqn:E'; try discriminate.
simpl in Henc.

simpl in H.
destruct (contains i (off, ty_size sub_ty)) eqn:E; try discriminate.
simpl in H.

assert (length l0 = ty_size sub_ty) as Hl0. {
  inversion Hprops.
  apply (PR_ENCODE_LEN _ H2 _ _ E').
}

refine (IH _ _ _ (write_subslice_at_index a off l0) _ _ vals _ _); auto.
{ inversion Hfit. auto. }
{ inversion Hprops. auto. }
{ apply write_subslice_length; auto.
  rewrite Hl0.
  inversion Hfit.
  simpl in H2.
  rewrite Ha_len.
  auto.
}
{ rewrite <- Hl0 in E.
  rewrite <- Hr.
  refine (subslice_write_nth_miss _ E).
  rewrite Hl0.
  rewrite Ha_len.
  inversion Hfit.
  simpl in H2.
  auto.
}
Qed.

Lemma encode_nth_miss {i vals l}
  (H : existsb (contains i) (map interval_of_field fields) = false)
  (Hi: i < size)
  (Hlens : length vals = length fields)
  (Henc: encode_tuple_fields (repeat Uninit size) fields encode vals = Some l)
: nth i l Uninit = Uninit.
Proof.
refine (encode_nth_rest fields_fit_size_l props_fields H Hi _ Hlens _ Henc).
{ apply repeat_length. }
{ apply nth_repeat. }
Qed.

Lemma encode_nth_hit {i l j vals} def
  (Hj : j < length fields)
  (Hvals_len : length vals = length fields)
  (H : encode_tuple_fields (repeat Uninit size) fields encode vals = Some l)
  (Hcont : contains i (interval_of_field (nth j fields (0,TBool))) = true)
: let (off, sub_ty) := nth j fields (0, TBool) in
exists subl, encode sub_ty (nth j vals def) = Some subl /\  nth i l Uninit = nth (i-off) subl Uninit.
Proof.
pose proof (repeat_length Uninit size) as Ha.
pose proof props_fields as Hprops.
pose proof fields_fit_size_l as Hfit.
pose proof fields_disjoint_l as Hdisj.

clear props_IH Hwf.

generalize dependent (repeat Uninit size).
generalize dependent vals.
generalize dependent j.

induction fields as [|f fs IH].
{ intros. simpl in Hj. lia. }

intros j Hj Hcont vals Hvals_len a H0 Ha.

destruct f as [off sub_ty] eqn:F.

destruct j as [|j]; cycle 1. {
  destruct vals as [|v vals]. { simpl in Hvals_len. lia. }
  simpl.
  simpl in H0.
  destruct (encode sub_ty v) eqn:E; cycle 1.
  { simpl in H0. discriminate H0. }
  refine (IH _ _ _ j _ _ vals _ (write_subslice_at_index a off l0) _ _); auto.
  { inversion Hprops. auto. }
  { inversion Hfit. auto. }
  { intros i' j1 j2 Hi' Hj1 Hj2 Hdiff Ht.
    refine (Hdisj i' (S j1) (S j2) Hi' _ _ _ _); simpl; try lia.
    auto.
  }
  { simpl in Hj. lia. }
  { apply write_subslice_length; auto.
    rewrite Ha.
    inversion Hprops.
    rewrite (PR_ENCODE_LEN _ H2 _ _ E).
    inversion Hfit.
    simpl in H6.
    auto.
  }
}

destruct vals as [|v vals].
{ simpl in *. discriminate Hvals_len. }

destruct (encode sub_ty v) eqn:E; cycle 1.
{ simpl in *. rewrite E in H0. discriminate. }

exists l0.
split. { auto. }
simpl in H0.

assert (length l0 = ty_size sub_ty) as Hl0. {
  inversion Hprops.
  apply (PR_ENCODE_LEN _ H2 _ _ E).
}

assert (off + length l0 <= length a) as Hfitl0. {
  rewrite Ha.
  rewrite Hl0.
  inversion Hfit.
  apply H2.
}

assert (nth i (write_subslice_at_index a off l0) Uninit = nth (i - off) l0 Uninit). {
  apply subslice_write_nth_hit; auto.
  { rewrite Hl0. auto. }
}

rewrite E in H0.
simpl in H0.

assert (i < size) as Hi. {
  unfold contains in Hcont.
  simpl in Hcont.
  destruct (andb_prop _ _ Hcont) as [_ Hil].
  destruct (Nat.ltb_spec i (off + ty_size sub_ty)); try discriminate Hil.
  assert (off + ty_size sub_ty <= size); cycle 1. { lia. }
  rewrite Ha in Hfitl0.
  rewrite <- Hl0.
  auto.
}

assert (length vals = length fs) as Hvfs_len.
{ simpl in Hvals_len. lia. }

refine (encode_nth_rest _ _ _ Hi _ Hvfs_len H _); auto; cycle 3.
{ apply write_subslice_length; auto. }
{ inversion Hfit. auto. }
{ inversion Hprops. auto. }

clear - Hdisj Hcont Hi.
simpl in Hcont.

assert (forall j, j < length fs -> contains i (interval_of_field (nth j fs (0,TBool))) = false). {
  intros j Hj.
  refine (Hdisj i 0 (S j) Hi _ _ _ _); try (simpl; lia).
  simpl. auto.
}
clear - H.

induction fs as [|[off sub_ty] fs IH].
{ simpl. auto. }

simpl.
assert (contains i (off, ty_size sub_ty) = false) as ->. {
  refine (H 0 _).
  simpl. lia.
}
simpl.
apply IH.
intros j Hj.
refine (H (S j) _).
simpl. lia.
Qed.

Lemma subslice_encode {l off sub_ty j vals def}
  (Hj : j < length fields)
  (Hvals_len : length vals = length fields)
  (Hfieldsj : nth j fields (0, TBool) = (off, sub_ty))
  (Hl: length l = size)
  (H : encode_tuple_fields (repeat Uninit size) fields encode vals = Some l)
: Some (subslice_with_length l off (ty_size sub_ty)) = encode sub_ty (nth j vals def).
Proof.
destruct (encode_nth_some def Hj Hvals_len Hfieldsj H) as (l' & Henc).
rewrite Henc.
f_equal.

assert (length (subslice_with_length l off (ty_size sub_ty)) = ty_size sub_ty). {
  rewrite subslice_length; auto.
  rewrite Hl.
  pose proof fields_fit_size_l as Hfit.
  pose proof (proj1 (Forall_nth _ _) Hfit) as Hfit_nth.
  assert (sub_ty = nth j (map snd fields) TBool) as ->. {
    rewrite (map_nth_switchd (0,TBool) _); auto.
    rewrite Hfieldsj.
    auto.
  }
  pose proof (Hfit_nth j (0,TBool) Hj).
  rewrite Hfieldsj in H0.
  simpl in H0.
  auto.
}

assert (length l' = ty_size sub_ty). {
  pose proof props_fields as Hprops.
  pose proof (proj1 (Forall_nth _ _) Hprops) as Hprops_nth.
  assert (sub_ty = nth j (map snd fields) TBool) as ->. {
    rewrite (map_nth_switchd (0,TBool) _); auto.
    rewrite Hfieldsj.
    auto.
  }
  assert (j < length (map snd fields)) as HF.
  { rewrite map_length. auto. }

  pose proof (Hprops_nth j TBool HF).
  apply (PR_ENCODE_LEN _ H1 _ _ Henc).
}

refine (nth_ext _ _ Uninit Uninit _ _).
{ rewrite H1. auto. }
intros i Hi.

assert (i < ty_size sub_ty).
{ rewrite <- H0. auto. }

rewrite subslice_nth; auto. {
  rewrite Hl.
  pose proof fields_fit_size_l as Hfit.
  pose proof (proj1 (Forall_nth _ _) Hfit) as Hfit_nth.
  assert (sub_ty = nth j (map snd fields) TBool) as ->. {
    rewrite (map_nth_switchd (0,TBool) _); auto.
    rewrite Hfieldsj.
    auto.
  }
  pose proof (Hfit_nth j (0,TBool) Hj).
  simpl in H3.
  rewrite Hfieldsj in H3.
  simpl in H3.
  auto.
}

assert (contains (i+off) (interval_of_field (nth j fields (0, TBool))) = true). {
  rewrite Hfieldsj.
  unfold contains.
  simpl.
  destruct (Nat.leb_spec off (i + off)); try lia.
  simpl.
  destruct (Nat.ltb_spec (i + off) (off + ty_size sub_ty)); lia.
}

pose proof (encode_nth_hit def Hj Hvals_len H H3).
rewrite Hfieldsj in H4.
destruct H4 as (l'' & Henc' & ->).
assert (l' = l'') as ->.
{ rewrite Henc' in Henc. inversion Henc. auto. }
f_equal.
lia.
Qed.

Lemma tuple_rt1 : rt1 t.
intros v [l Hdec].
destruct (tuple_dec Hdec) as (Hlen & vals & Htr & -> & l' & Henc & Hlen').
exists l'.
split. { auto. }
unfold decode. fold decode. unfold decode_tuple.

assert (length vals = length fields) as Hvals_len. {
  rewrite <- (transpose_len Htr).
  rewrite map_length.
  auto.
}

assert (transpose (map (decode_tuple_field decode l') fields) = Some vals); cycle 1. {
  rewrite H.
  simpl.
  rewrite (tuple_encode_len _ _ Henc).
  simpl.
  rewrite Nat.eqb_refl.
  auto.
}

assert (encode_tuple_fields (repeat Uninit size) fields encode vals = Some l'). {
  unfold encode in Henc. fold encode in Henc. unfold encode_tuple in Henc.
  simpl in Henc.
  unfold assuming in Henc.
  rewrite Hvals_len in Henc.
  rewrite Nat.eqb_refl in Henc.
  simpl in Henc.
  auto.
}

apply (transpose_nth_ext (VBool true)).
{ rewrite map_length. auto. }

intros def j Hj.
rewrite map_length in Hj.
rewrite (map_nth_switchd (0,TBool)); auto.
destruct (nth j fields (0, TBool)) as [off sub_ty] eqn:Hfieldsj.
unfold decode_tuple_field.
rewrite Hfieldsj.

assert (rt1 sub_ty) as Hsub_rt1. {
  pose proof props_fields as Hprops.
  pose proof (proj1 (Forall_nth _ _) Hprops) as Hprops_nth.
  assert (sub_ty = nth j (map snd fields) TBool) as ->. {
    rewrite (map_nth_switchd (0,TBool) _); auto.
    rewrite Hfieldsj.
    auto.
  }
  refine (PR_RT1 _ (Hprops_nth j _ _)).
  rewrite map_length. auto.
}

assert (Some (subslice_with_length l' off (ty_size sub_ty)) = encode sub_ty (nth j vals def)); cycle 1. {
  assert (decode_tuple_field decode l (nth j fields (0,TBool)) = Some (nth j vals def)). {
    pose proof (transpose_nth Htr).
    rewrite <- H1; cycle 1. { rewrite map_length. auto. }
    rewrite (map_nth_switchd (0,TBool)); auto.
  }
  assert (is_valid_for sub_ty (nth j vals def)). {
    unfold decode_tuple_field in H1.
    rewrite Hfieldsj in H1.
    eexists _.
    apply H1.
  }
  destruct (Hsub_rt1 _ H2) as (lsub & Hsubenc & Hsubdec).
  assert (lsub = subslice_with_length l' off (ty_size sub_ty)) as <-; cycle 1. { auto. }
  rewrite <- H0 in Hsubenc.
  inversion Hsubenc.
  auto.
}

apply subslice_encode; auto.
Qed.

Lemma tuple_rt2 : rt2 t.
intros l v Hdec.
destruct (tuple_dec Hdec) as (Hlen & vals & Htr & -> & l' & Henc & Hlen').
exists l'.
split. { auto. }
apply (le_nth Uninit). { lia. } 
intros i Hi.

pose proof fields_fit_size_l as Hfit.
pose proof (proj1 (Forall_nth _ _) Hfit) as Hfit_nth.

pose proof props_fields as Hprops.
pose proof (proj1 (Forall_nth _ _) Hprops) as Hprops_nth.

assert (length vals = length fields) as Hvals_len. {
  pose proof transpose_len Htr.
  rewrite <- H.
  rewrite map_length.
  auto.
}

destruct (existsb (contains i) (map interval_of_field fields)) eqn:Hex; cycle 1. {
  unfold encode in Henc. fold encode in Henc. unfold encode_tuple in Henc.
  simpl in Henc.
  unfold assuming in Henc.
  rewrite Hvals_len in Henc.
  rewrite (Nat.eqb_refl (length fields)) in Henc.
  simpl in Henc.
  rewrite (encode_nth_miss Hex _ Hvals_len Henc).
  { rewrite <- Hlen'. auto. }
  simpl.
  auto.
}

destruct (proj1 (existsb_exists _ _) Hex) as (interval & Hin & Hcont).
destruct (In_nth _ _ (0,0) Hin) as [j [Hj Hnth]].
rewrite map_length in Hj.

unfold encode in Henc. fold encode in Henc. unfold encode_tuple in Henc.
simpl in Henc.
unfold assuming in Henc.
rewrite Hvals_len in Henc.
rewrite (Nat.eqb_refl (length fields)) in Henc.
simpl in Henc.

destruct (nth j fields (0, TBool)) as [off sub_ty] eqn:Hdestr.

assert (off + ty_size sub_ty <= size) as Hfitsub. {
  pose proof Hfit_nth j (0, TBool) Hj.
  rewrite Hdestr in H.
  simpl in H.
  auto.
}

assert (interval = (off, ty_size sub_ty)) as ->. {
  rewrite (map_nth_switchd (0, TBool)) in Hnth; auto.
  rewrite Hdestr in Hnth.
  auto.
}

assert (contains i (interval_of_field (nth j fields (0, TBool))) = true) as Hcont'. {
  rewrite <- Hcont.
  f_equal.
  rewrite Hdestr.
  auto.
}

assert (off <= i /\ i < off + ty_size sub_ty) as [Ho1 Ho2]. {
  unfold contains in Hcont.
  simpl in Hcont.
  destruct (andb_prop _ _ Hcont) as [A B].
  split.
  { destruct (Nat.leb_spec off i); lia. }
  { destruct (Nat.ltb_spec i (off + ty_size sub_ty)); lia. }
}

pose proof (encode_nth_hit (VBool true) Hj Hvals_len Henc Hcont') as F.
rewrite Hdestr in F.
destruct F as (subl & Hsubenc & ->).

assert (j < length (map (decode_tuple_field decode l) fields)) as H''.
{ rewrite map_length. auto. }
pose proof (transpose_nth Htr (VBool true) j H'').
rewrite (map_nth_switchd (0,TBool) Hj) in H.
unfold decode_tuple_field in H.
rewrite Hdestr in H.
simpl in H.
replace (nth i l Uninit) with (nth (i-off+off) l Uninit); cycle 1.
{ f_equal. lia. }

rewrite <- (@subslice_nth _ off (ty_size sub_ty) (i-off) l Uninit); try lia.
apply le_nth_rev. { apply le_abstract_byte_refl. }
remember (nth j vals (VBool true)) as v.
assert (Props sub_ty) as Hsubprops. {
  assert (j < length (map snd fields)) as H'. { rewrite map_length. auto. }
  pose proof (Hprops_nth j TBool H').
  rewrite (map_nth_switchd (0,TBool)) in H0; auto.
  rewrite Hdestr in H0.
  auto.
}

destruct (PR_RT2 _ Hsubprops _ _ H) as (ll & B & C).
assert (subl = ll) as ->. {
  rewrite B in Hsubenc.
  inversion Hsubenc.
  auto.
}

auto.
Qed.

Lemma tuple_mono1 : mono1 t.
Admitted.

Lemma tuple_mono2 : mono2 t.
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
