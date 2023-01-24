From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils subslice le.
Require Import List Nat PeanoNat Bool Lia.
Import ListNotations.

Section union.

Context {params: Params}.
Context {fields: Fields}.
Context {chunks: Chunks}.
Context {size: Size}.
Notation t := (TUnion fields chunks size).
Context (Hwf: wf t).

Lemma chunks_fit_size_l : chunks_fit_size chunks size.
apply Hwf.
Qed.

Lemma chunks_fit_size_nth j :
  let (offset,len) := nth j chunks (0, 0) in
  size >= offset + len.
Proof.
have H chunks_fit_size_l.
clear - chunks H.
generalize dependent chunks.
induction j as [|j IH].
{ intros.
  destruct chunks0. { simpl. lia. }
  simpl. destruct p as [off len].
  inversion H.
  simpl in H2.
  auto.
}

intros.
destruct chunks0. { simpl. lia. }
simpl.
apply IH.
inversion H.
auto.
Qed.


Lemma chunks_disjoint_l : ForallOrdPairs interval_pair_sorted_disjoint chunks.
apply Hwf.
Qed.

Lemma chunk_size_lemma {l} (Hlen: length l = size) :
  forallb check_chunk_size (combine chunks (map (decode_union_chunk l) chunks)) = true.
Proof.
apply forallb_forall.
apply Forall_forall.
have Hfit chunks_fit_size_l.
unfold chunks_fit_size in Hfit.
clear Hwf.

induction chunks as [|c chunks' IH].
{ apply Forall_nil. }

simpl (map _ _).
simpl (combine _ _).
apply Forall_cons; cycle 1.
{ apply IH. inversion Hfit. auto. }

clear IH.
unfold check_chunk_size.
unfold decode_union_chunk.
destruct c as [offset len].
inversion Hfit.
simpl in H1.
apply Nat.eqb_eq.
rewrite subslice_length. { auto. }
rewrite Hlen.
auto.
Qed.

Lemma union_dec [l v] (H: decode t l = Some v) :
  length l = size /\
  exists data, v = VUnion data /\
  data = map (decode_union_chunk l) chunks /\
  forallb check_chunk_size (combine chunks data) = true /\
  encode t v = Some (fold_left encode_union_chunk
       (combine chunks data) (repeat Uninit size) ).
Proof.
unfold decode,decode_union in H.
assert (length l = size) as Hlen.
{ destruct (Nat.eqb_spec (length l) size); auto. simpl in H. discriminate H. }
split. { auto. }

rewrite Hlen in H.
rewrite Nat.eqb_refl in H.
simpl in H.
inversion H. clear H v H1.
unfold encode,encode_union.
simpl.
unfold assuming.
rewrite (map_length (decode_union_chunk l) chunks).
rewrite Nat.eqb_refl.
simpl.
rewrite (chunk_size_lemma Hlen).
eexists _.
split. { auto. }
split. { auto. }
simpl.
auto.
split. { apply (chunk_size_lemma Hlen). }
auto.
Qed.

Lemma fold_left_step {A B} (f: A -> B -> A) x l a :
fold_left f (x::l) a = fold_left f l (f a x).
Proof.
simpl.
auto.
Qed.

Lemma fold_encode_length {data}
  (Hc : forallb check_chunk_size (combine chunks data) = true)
  (Hlen : length data = length chunks) :
length (fold_left encode_union_chunk (combine chunks data) (repeat Uninit size)) = size.
Proof.
have Hfit chunks_fit_size_l.
unfold chunks_fit_size in Hfit.
clear Hwf.

assert (
  forall a, length a = size ->
  length (fold_left encode_union_chunk (combine chunks data) a) = size
) as Hsub; cycle 1.
{ apply Hsub. apply repeat_length. }

generalize dependent chunks.

induction data as [|x data IH].
{ intros. rewrite combine_nil. simpl. auto. }

intros.
destruct chunks0. { simpl. auto. }

simpl (combine _ _).
rewrite fold_left_step.
assert (length (encode_union_chunk a (p, x)) = size). {
  unfold encode_union_chunk.
  destruct p as [offset len].
  apply write_subslice_length. { auto. }
  inversion Hfit.
  simpl in H2.
  rewrite H.
  replace (length x) with len. { auto. }
  simpl in Hc.
  destruct (len =? length x) eqn:E; cycle 1. { simpl in Hc. discriminate Hc. }
  apply Nat.eqb_eq.
  auto.
}

apply IH.
- simpl in Hc.
  destruct (forallb check_chunk_size (combine chunks0 data))%bool; auto.
  rewrite andb_false_r in Hc. discriminate Hc.
- simpl in Hlen. inversion Hlen. auto.
- inversion Hfit. auto.
- auto.
Qed.

Lemma rt_map_step2 {a offset cs d data}
  (Hlen_a : length a = size)
  (Ha: subslice_with_length a offset (length d) = d)
  (Hc : forallb check_chunk_size (combine cs data) = true)
  (Hlen : length data = length cs)
  (Hfit: chunks_fit_size ((offset,length d)::cs) size)
  (Hdisj: ForallOrdPairs interval_pair_sorted_disjoint ((offset,length d)::cs)) :
  subslice_with_length (fold_left encode_union_chunk (combine cs data) a) offset (length d) = d.
Proof.
generalize dependent cs.
generalize dependent a.
induction data as [|d' data IH].
{ intros. rewrite combine_nil. simpl. auto. }

intros.
destruct cs as [|[offset' len'] cs].
{ discriminate Hlen. }

assert (len' = length d') as -> .
{ simpl in Hc. destruct (Nat.eqb_spec len' (length d')); auto. discriminate Hc. }

simpl (combine _ _).
rewrite fold_left_step.
apply IH.
- unfold encode_union_chunk.
  apply write_subslice_length; auto.
  inversion Hfit. inversion H2.
  simpl in H5.
  rewrite Hlen_a.
  simpl in Hc.
  auto.
- assert (interval_pair_sorted_disjoint (offset, length d) (offset', length d')). {
    unfold encode_union_chunk.
    inversion Hdisj.
    inversion H1.
    auto.
  }
  unfold interval_pair_sorted_disjoint in H.
  unfold encode_union_chunk.
  apply subslice_independent_write; auto.
- simpl in Hc. rewrite Nat.eqb_refl in Hc. auto.
- auto.
- inversion Hfit.
  apply Forall_cons. { auto. }
  inversion H2.
  auto.
- inversion Hdisj.
  apply FOP_cons.
  -- inversion H1. auto.
  -- inversion H2. auto.
Qed.

Lemma rt_map_step {a offset cs d data}
  (Hlen_a : length a = size)
  (Hc : forallb check_chunk_size (combine cs data) = true)
  (Hlen : length data = length cs)
  (Hfit: chunks_fit_size ((offset,length d)::cs) size)
  (Hdisj: ForallOrdPairs interval_pair_sorted_disjoint ((offset,length d)::cs)) :
  subslice_with_length
    (fold_left
      encode_union_chunk
      (combine cs data)
      (write_subslice_at_index a offset d)
    )
    offset
    (length d) = d.
Proof.
apply rt_map_step2; auto.
- apply write_subslice_length. auto.
  unfold chunks_fit_size in Hfit.
  inversion Hfit.
  simpl in H1. rewrite Hlen_a. auto.
- apply subslice_rt.
  inversion Hfit.
  simpl in H1.
  lia.
Qed.

Lemma rt_map {cs data}
  (Hc : forallb check_chunk_size (combine cs data) = true)
  (Hlen : length data = length cs)
  (Hfit: chunks_fit_size cs size)
  (Hdisj: ForallOrdPairs interval_pair_sorted_disjoint cs) :
map (decode_union_chunk
    (fold_left encode_union_chunk (combine cs data) (repeat Uninit size))
    ) cs = data.
Proof.
declare a Ha (repeat Uninit size).
rewrite Ha.
assert (Ha_len: length a = size).
{ rewrite <- Ha. apply repeat_length. }

clear Ha.

generalize dependent cs.
generalize dependent a.
induction data as [|d data IH].
{ intros. destruct cs; auto. discriminate Hlen. }

intros.
destruct cs as [|c cs]. { discriminate Hlen. }

simpl (combine _ _).
rewrite fold_left_step.
simpl (encode_union_chunk (repeat Uninit size) (c,d)).
destruct c as [offset len].
simpl.
f_equal. {
  assert (len = length d) as ->.
  { simpl in Hc. destruct (Nat.eqb_spec len (length d)); auto. discriminate Hc. }
  apply rt_map_step; auto.
  - simpl in Hc.
    rewrite Nat.eqb_refl in Hc.
    auto.
}

apply IH.
- apply write_subslice_length. { auto. }
  simpl in Hc.
  rewrite Ha_len.
  replace (length d) with len.
  inversion Hfit.
  simpl in H1. lia.
  destruct (Nat.eqb_spec len (length d)); auto. simpl in Hc. discriminate Hc.
- simpl in Hc. destruct ((len =? length d)). simpl in Hc. auto. simpl in Hc. discriminate Hc.
- simpl in Hlen. auto.
- inversion Hfit. auto.
- inversion Hdisj. auto.
Qed.

Lemma union_rt1 : rt1 t.
Proof.
intros v [l Hdec].
destruct (union_dec Hdec) as (Hlen & data & -> & Hdata & Hfor & Henc).
eexists _.
split. { apply Henc. }
unfold decode,decode_union.
simpl.
assert (length data = length chunks) as Hdata_len.
{ rewrite Hdata. apply map_length. }

rewrite (fold_encode_length Hfor Hdata_len).
rewrite Nat.eqb_refl.
simpl.
do 2 f_equal.
apply (rt_map Hfor Hdata_len chunks_fit_size_l chunks_disjoint_l).
Qed.

Lemma fold_encode_nth_miss_rest {a cs data i r}
  (H : existsb (contains i) cs = false)
  (Ha_len : length a = size)
  (Ha: nth i a Uninit = r)
  (Hdlen : length data = length cs)
  (Hfit: chunks_fit_size cs size)
  (Hfor : forallb check_chunk_size (combine cs data) = true) :
nth i (fold_left encode_union_chunk (combine cs data) a) Uninit
= r.
Proof.
generalize dependent a.
generalize dependent data.
induction cs as [|c ch IH].
{ intros. simpl. auto. }

destruct c as [off len].
intros.
destruct data as [|d data].
{ simpl in Hdlen. lia. }

simpl.

assert (length d = len) as Hdlen'. {
  simpl in Hfor.
  destruct (andb_prop _ _ Hfor) as [HX _].
  destruct (Nat.eqb_spec len (length d)); auto.
  lia.
}

assert (off + length d <= length a). {
  rewrite Hdlen'.
  assert (length a = size) as ->. { auto. }
  inversion Hfit.
  auto.
}

apply IH.
{ simpl in H. destruct (orb_false_elim _ _ H). auto. }
{ inversion Hfit. auto. }
{ simpl in Hdlen. lia. }
{ simpl in Hfor. apply (andb_prop _ _ Hfor). }
{ apply write_subslice_length; lia. }

assert (contains i (off, length d) = false). {
  simpl in H.
  destruct (orb_false_elim _ _ H).
  rewrite Hdlen'.
  auto.
}

rewrite subslice_write_nth_miss; auto.
Qed.

Lemma fold_encode_nth_miss {data i}
  (H : existsb (contains i) chunks = false)
  (Hdlen : length data = length chunks)
  (Hfor : forallb check_chunk_size (combine chunks data) = true) :
nth i (fold_left encode_union_chunk (combine chunks data) (repeat Uninit size)) Uninit
= Uninit.
Proof.
apply fold_encode_nth_miss_rest; auto.
{ apply repeat_length. }
{ apply nth_repeat. }
{ apply chunks_fit_size_l. }
Qed.

Lemma fold_encode_nth_hit {data i j}
  (Hj: j < length chunks)
  (H : contains i (nth j chunks (0,0)) = true)
  (Hdlen : length data = length chunks)
  (Hfor : forallb check_chunk_size (combine chunks data) = true) :
let data_ := nth j data [] in
let chunk_ := nth j chunks (0,0) in
nth i (fold_left encode_union_chunk (combine chunks data) (repeat Uninit size)) Uninit
= nth (i-fst chunk_) data_ Uninit.
Proof.
declare chunk_ Hc (nth j chunks (0,0)).
declare data_ Hd (nth j data []).
rewrite Hd,Hc.
simpl.

have Hfit chunks_fit_size_l.
have Hdisj chunks_disjoint_l.
clear Hwf.

(* we need to be generic over a, i.e. (repeat Uninit size) *)
(* j needs to be decreased in each iteration, hence j needs to be generalize-dep as well *)

assert (forall a, length a = size -> nth i
  (fold_left encode_union_chunk (combine chunks data)
     a) Uninit =
nth (i - fst chunk_) data_ Uninit); cycle 1.
{ apply H0. apply repeat_length. }

generalize dependent data.
generalize dependent j.
induction chunks as [|c cs IH].
{ intros. simpl in Hj. lia. }

intros.
destruct data as [|d data].
{ simpl in Hdlen. lia. }

destruct c as [off len].
simpl.

assert (len = length d). {
  simpl in Hfor.
  destruct (andb_prop _ _ Hfor).
  destruct (Nat.eqb_spec len (length d)); lia.
}

(* in this proof, the case j=0 is the hard one. *)
destruct j as [|j]; cycle 1. {
  assert (chunks_fit_size cs size) as HA1.
  { inversion Hfit. auto. }

  assert (ForallOrdPairs interval_pair_sorted_disjoint cs) as HA2.
  { inversion Hdisj. auto. }

  apply (IH HA1 HA2 j); auto.
  { simpl in Hj. lia. }
  { simpl in Hfor.
    destruct (andb_prop _ _ Hfor).
    auto.
  }
  { apply write_subslice_length; auto. 
    rewrite H0.
    inversion Hfit.
    rewrite <- H1.
    auto.
  }
}

assert (off + length d <= length a). {
  inversion Hfit.
  simpl in H4.
  rewrite <- H1.
  rewrite H0.
  auto.
}

assert (nth i (write_subslice_at_index a off d) Uninit
      = nth (i - off) d Uninit). {
  apply subslice_write_nth_hit; auto.
  simpl in H.
  rewrite <- H1.
  auto.
}

assert (existsb (contains i) cs = false). {
  simpl in H.
  clear - cs Hdisj H.
  induction cs as [|c cs IH]. { simpl. auto. }

  simpl.
  assert (contains i c = false) as ->. {
    unfold contains in *.
    destruct c as [off' len'].
    inversion Hdisj.
    inversion H2.
    unfold interval_pair_sorted_disjoint in H6.
    simpl in *.
    clear - H6 off len off' len' i H.
    assert (off' > i); cycle 1. {
      destruct (Nat.leb_spec off' i); auto; lia.
    }
    destruct (andb_prop _ _ H).
    assert (off <= i). {
      destruct (Nat.leb_spec off i); auto; lia.
    }
    assert (i < off + len). {
      destruct (Nat.ltb_spec i (off+len)); auto; lia.
    }
    lia.
  }
  simpl.
  apply IH.
  inversion Hdisj.
  inversion H2.
  apply FOP_cons.
  auto.
  inversion H3.
  auto.
}

apply fold_encode_nth_miss_rest; auto.
{ apply write_subslice_length; auto. }
{ assert (fst chunk_ = off) as ->. { simpl in Hc. rewrite <- Hc. auto. }
  assert (data_ = d) as ->. { simpl in Hd. auto. }
  auto.
}
{ inversion Hfit. auto. }
{ simpl in Hfor. destruct (andb_prop _ _ Hfor). auto. }
Qed.

Lemma union_rt2 : rt2 t.
Proof.
intros l v Hdec.
destruct (union_dec Hdec) as (Hlen & data & -> & Hdata & Hfor & Henc).
eexists _.
split. { apply Henc. }

assert (length (fold_left encode_union_chunk (combine chunks data)
        (repeat Uninit size)) = size) as Hlen_enc.
{ rewrite fold_encode_length; auto. rewrite Hdata. apply map_length. }
apply (le_nth Uninit). { rewrite Hlen_enc. auto. }

intros i Hi.
rewrite Hlen_enc in Hi.
assert (length data = length chunks) as Hdlen.
{ rewrite Hdata. apply map_length. }

destruct (existsb (contains i) chunks) eqn:Hex; cycle 1. {
  rewrite (fold_encode_nth_miss Hex Hdlen Hfor).
  simpl. auto.
}

destruct (proj1 (existsb_exists _ _) Hex) as (chunk & Hin & Hcont).
destruct (In_nth _ _ (0,0) Hin) as [j [Hj Hnth]].
assert (contains i (nth j chunks (0,0)) = true).
{ rewrite <- Hnth in Hcont. auto. }

rewrite (fold_encode_nth_hit Hj H Hdlen Hfor).
assert ((nth (i - fst (nth j chunks (0, 0)))
   (nth j data []) Uninit) = nth i l Uninit); cycle 1.
{ rewrite H0. apply le_abstract_byte_refl. }

rewrite Hdata.
replace ([]) with (decode_union_chunk l (0,0)); cycle 1.
{ simpl. rewrite (subslice_zero l). simpl. auto. }
rewrite map_nth.
(* why does rewrite not work here? *)
assert (nth j chunks (0, 0) = chunk) as ->. { auto. }
unfold decode_union_chunk.
destruct chunk as [off len]. simpl.
unfold contains in Hcont. simpl in Hcont.
destruct (andb_prop _ _ Hcont) as [Hi_off Hi_range].
assert (off <= i). { apply Nat.leb_le. auto. }
assert (i < off + len). { apply Nat.ltb_lt. auto. }
rewrite subslice_nth; try lia.
{ f_equal. lia. }

rewrite Hlen.
have A (chunks_fit_size_nth j).
replace (nth j chunks (0,0)) with (off, len) in A. { auto. }
Qed.

Lemma union_mono1 : mono1 t.
Proof.
intros v1 v2 Hle [l1 Hdec1] [l2 Hdec2].
destruct (union_dec Hdec1) as (Hlen1 & data1 & -> & Hdata1 & Hfor1 & Henc1).
destruct (union_dec Hdec2) as (Hlen2 & data2 & -> & Hdata2 & Hfor2 & Henc2).
eexists _, _.
split. { apply Henc1. }
split. { apply Henc2. }

assert (length data1 = length chunks) as Hd1.
{ rewrite Hdata1. apply map_length. }

assert (length data2 = length chunks) as Hd2.
{ rewrite Hdata2. apply map_length. }

assert (length (fold_left encode_union_chunk (combine chunks data1) (repeat Uninit size)) = size) as Hdlen1.
{ rewrite fold_encode_length; auto. }

assert (length (fold_left encode_union_chunk (combine chunks data2) (repeat Uninit size)) = size) as Hdlen2.
{ rewrite fold_encode_length; auto. }

apply (le_nth Uninit). { lia. }

intros i Hi.
rewrite Hdlen1 in Hi.

destruct (existsb (contains i) chunks) eqn:Hex; cycle 1. {
  rewrite fold_encode_nth_miss; auto.
  rewrite fold_encode_nth_miss; auto.
  simpl. auto.
}

destruct (proj1 (existsb_exists _ _) Hex) as (chunk & Hin & Hcont).
destruct (In_nth _ _ (0,0) Hin) as [j [Hj Hnth]].
assert (contains i (nth j chunks (0,0)) = true).
{ rewrite <- Hnth in Hcont. auto. }

rewrite (fold_encode_nth_hit Hj H Hd1 Hfor1).
rewrite (fold_encode_nth_hit Hj H Hd2 Hfor2).

unfold le,Value_DefinedRelation in Hle.
destruct (nth j chunks (0,0)) as [off len].
simpl (fst _).

apply le_nth_rev. { apply le_abstract_byte_refl. }
apply le_nth_rev. { apply le_list_abstract_byte_refl. }
auto.
Qed.

Lemma union_mono2 : mono2 t.
Admitted.

Lemma union_encode_len : encode_len t.
Proof.
intros v l Henc.
unfold encode,encode_union in Henc.
destruct v; try discriminate Henc.
unfold assuming in Henc.
simpl in Henc.
destruct (length l0 =? length chunks) eqn:Hlen; try discriminate Henc.
simpl in Henc.
destruct (forallb check_chunk_size (combine chunks l0)) eqn:Hcheck; try discriminate Henc.
simpl in Henc.
inversion Henc.
apply fold_encode_length; auto.
destruct (Nat.eqb_spec (length l0) (length chunks)); auto.
discriminate Hlen.
Qed.

Lemma union_props : Props t.
Proof.
split.
- auto.
- apply union_rt1.
- apply union_rt2.
- apply union_mono1.
- apply union_mono2.
- apply union_encode_len.
Qed.

End union.
