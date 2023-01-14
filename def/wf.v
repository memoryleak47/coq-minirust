Require Import ZArith List Permutation Coq.Program.Tactics Coq.Program.Wf Nat Lia.
Import ListNotations.
From Minirust.def Require Import ty int_encoding.

Section wf.

Context {params: Params}.

Definition valid_size (size: Size) : Prop := (int_in_range (Z.of_nat size) PTR_SIZE Signed) = true.

Definition fields_fit_size (fields: Fields) (size : Size) :=
  forall f, f < length fields ->
  match nth f fields (0,TBool) with
  | (start,ty) => size >= start + ty_size ty
  end.

Definition chunks_fit_size (chunks: Chunks) (size: Size) :=
  forall c, c < length chunks ->
  match nth c chunks (0,0) with
  | (offset,len) => size >= offset+len
  end.

(* an interval is (offset, size) in bytes *)
Notation Interval := (Size * Size)%type.

(* checks whether i1 is fully contained in i2 *)
Definition interval_pair_contained_in (i1 i2: Interval) :=
  match (i1,i2) with
  | ((o1,s1), (o2,s2)) => o2 <= o1 /\ o2+s2 >= o1+s2
  end.

(* checks whether i1 and i2 are disjoint *)
Definition interval_pair_disjoint (i1 i2: Interval) :=
  match (i1,i2) with
  | ((o1,s1), (o2,s2)) => o1+s1 <= o2 \/ o2+s2 <= o1
  end.

Definition intervals_disjoint (l: list Interval) :=
  forall i j, i < length l -> j < length l -> i <> j ->
  interval_pair_disjoint (nth i l (0,0)) (nth j l (0,0)).

Definition interval_of_field (f: Size * Ty) :=
  match f with
  | (o,t) => (o, ty_size t)
  end.

Definition fields_disjoint (fields: Fields) : Prop :=
  intervals_disjoint (map interval_of_field fields).

(* checks that every field is completely contained a chunk *)
(* note that a chunk is already an `Interval` *)
Definition fields_in_chunks (fields: Fields) (chunks: Chunks) :=
  forall f, f < length fields ->
  exists c, c < length chunks ->
  interval_pair_contained_in (interval_of_field (nth f fields (0,TBool))) (nth c chunks (0,0)).

Definition chunks_disjoint (chunks: Chunks) := intervals_disjoint chunks.
Definition chunks_sorted (chunks: Chunks) :=
  forall i j, i < length chunks -> j < length chunks -> i < j ->
  fst (nth i chunks (0,0)) <= fst (nth j chunks (0,0)).

Fixpoint pow2 (x: nat) :=
  match x with
  | 0 => 1
  | S y => 2 * pow2 y
  end.

Fixpoint ty_depth (t: Ty) : nat :=
  match t with
  | TBool => 0
  | TInt _ _ => 0
  | TPtr _ _ => 0
  | TArray e _ => S (ty_depth e)
  | TTuple fields _ => S (list_max (map (fun x => ty_depth (snd x)) fields))
  | TUnion fields _ _ => S (list_max (map (fun x => ty_depth (snd x)) fields))
  end.

Program Fixpoint wf (t: Ty) {measure (ty_depth t)} : Prop :=
  valid_size (ty_size t)
  /\
  match t with
  | TInt size signedness => exists n, (pow2 n) = size
  | TBool => True
  | TPtr _ _ => True
  | TTuple fields size => fields_fit_size fields size
                      /\ forall f, f < length fields ->
                           match nth f fields (0,TBool) with
                           | (start,ty) => wf ty
                           end
                      /\ fields_disjoint fields
  | TArray elem_ty count => wf elem_ty
                        /\ (count >= 0)%Z
  | TUnion fields chunks size => fields_fit_size fields size
                             /\   forall f, f < length fields ->
                                  match nth f fields (0,TBool) with
                                  | (start,ty) => wf ty
                                  end
                             /\ fields_in_chunks fields chunks
                             /\ chunks_disjoint chunks
                             /\ chunks_sorted chunks
                             /\ chunks_fit_size chunks size
  end.


(* prove of the well-formedness of the recursion within wf: *)

Lemma wf_helper {a i l}
  (H1: i < length l)
  (H2: nth i l 0 = a):
  a < S (list_max l).
Proof.
assert (a <= list_max l); cycle 1. { lia. }
assert (In a l).
{ rewrite <- H2. apply (nth_In l 0 H1). }

clear H2 H1 i.
destruct (Nat.leb_spec a (list_max l)). { auto. }
destruct l. { simpl in H. contradict H. }

assert (Forall (fun x => x < a) (n::l)). {
  apply list_max_lt. { intros A. discriminate A. }
  auto.
}

assert (forall x, In x (n::l) -> x < a). {
  apply Forall_forall.
  auto.
}

assert (a < a). { apply (H2 _ H). }
lia.
Qed.

Next Obligation.
simpl (ty_depth (TTuple fields size)).
destruct (Nat.ltb_spec f (length fields)); cycle 1. {
  rewrite nth_overflow in Heq_anonymous.
  inversion Heq_anonymous.
  simpl. lia. auto.
}

assert (f < length ((map (fun x : Size * Ty => ty_depth (snd x)) fields))).
{ rewrite map_length. auto. }

apply (wf_helper H0).
set (f_ := (fun x : Size * Ty => ty_depth (snd x))).
replace 0 with ( f_ (0,TBool)); cycle 1.
{ simpl. auto. }

rewrite map_nth.
replace ((nth f fields (0, TBool))) with (start, ty); auto.
Qed.

Next Obligation.
simpl (ty_depth (TUnion fields chunks size)).
destruct (Nat.ltb_spec f (length fields)); cycle 1. {
  rewrite nth_overflow in Heq_anonymous.
  inversion Heq_anonymous.
  simpl. lia. auto.
}

assert (f < length ((map (fun x : Size * Ty => ty_depth (snd x)) fields))).
{ rewrite map_length. auto. }

apply (wf_helper H0).
set (f_ := (fun x : Size * Ty => ty_depth (snd x))).
replace 0 with ( f_ (0,TBool)); cycle 1.
{ simpl. auto. }

rewrite map_nth.
replace ((nth f fields (0, TBool))) with (start, ty); auto.
Qed.

End wf.