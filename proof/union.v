From Minirust.def Require Import ty encoding thm wf le utils.
From Minirust.proof Require Import defs.
From Minirust.proof.lemma Require Import utils subslice.
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

Lemma chunks_disjoint_l : ForallOrdPairs interval_pair_sorted_disjoint chunks.
apply Hwf.
Qed.

Lemma fold_left_step {A B} (f: A -> B -> A) x l a :
fold_left f (x::l) a = fold_left f l (f a x).
Proof.
simpl.
auto.
Qed.

(* returns the chunk the idx'th byte belongs to, or None if it is not part of a chunk *)
(* return (chunk_index, offset of that chunk, len of that chunk, data of that chunk) *)
(* can be called with `data = []` if you don't care for the data *)
Definition get_chunk (idx: nat) (data: list (list AbstractByte)): option (nat * Size * Size * list AbstractByte) :=
  (fix get_chunk cs data i :=
    match cs with
    | (offset,len)::cs' =>
      if ((offset <=? idx) && (idx <=? offset + len)) then
        Some (i, offset, len, hd [] data)
      else
        get_chunk cs' (tl data) (S i)
    | [] => None
    end
  ) chunks data 0.

(* TODO add similar decode eqn *)
Lemma encode_eqn {data}
  (Hc : forallb check_chunk_size (combine chunks data) = true)
  (Hlen : length data = length chunks) :
forall i, i < size ->
nth i (fold_left encode_union_chunk (combine chunks data) (repeat Uninit size)) Uninit
  = match get_chunk i data with
    | Some tup =>
      match tup with
      | (_,offset,len,d) => nth (i-offset) d Uninit
      end
    | None => Uninit
   end.
Proof.
intros i Hi.
assert(Hfit: chunks_fit_size chunks size). { apply chunks_fit_size_l. }
assert (Hdisj: ForallOrdPairs interval_pair_sorted_disjoint chunks). { apply chunks_disjoint_l. }
clear Hwf.
unfold get_chunk.
induction chunks as [|c cs IH].
{ simpl. apply nth_repeat. }

destruct c as [offset len].
destruct ((offset <=? i) && (i <=? offset + len)) eqn:E. {
  simpl.
  destruct data as [|d data]. { discriminate Hlen. }
  simpl (hd _ _).
  rewrite fold_left_step.
  simpl.
  admit.
}
Admitted.

(* another approach on proving rt_map by using nth *)
Lemma rt_map_nth {cs data}
  (Hc : forallb check_chunk_size (combine cs data) = true)
  (Hlen : length data = length cs)
  (Hfit: chunks_fit_size cs size)
  (Hdisj: ForallOrdPairs interval_pair_sorted_disjoint cs) :
map (decode_union_chunk
    (fold_left encode_union_chunk (combine cs data) (repeat Uninit size))
    ) cs = data.
Admitted.

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
Admitted.

Lemma union_rt2 : rt2 t.
Proof.
intros l v Hdec.
destruct (union_dec Hdec) as (Hlen & data & -> & Hdata & Hfor & Henc).
eexists _.
split. { apply Henc. }
(* it seems like we need another large Lemma like rt_map for this. Maybe we can re-use it somehow? *)
Admitted.

Lemma union_mono1 : mono1 t.
Proof.
intros v1 v2 Hle [l1 Hdec1] [l2 Hdec2].
destruct (union_dec Hdec1) as (Hlen1 & data1 & -> & Hdata1 & Hfor1 & Henc1).
destruct (union_dec Hdec2) as (Hlen2 & data2 & -> & Hdata2 & Hfor2 & Henc2).
eexists _, _.
split. { apply Henc1. }
split. { apply Henc2. }
Admitted.

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
