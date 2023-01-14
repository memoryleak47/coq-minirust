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

(* This is a fixpoint so that Coq doesn't consider it to be ill-formed *)
Definition fields_wf (fields: Fields) (wf_call: Ty -> Prop) :=
(fix fields_wf (fields: Fields) :=
  match fields with
  | [] => True
  | (_, ty)::fields' => wf_call ty /\ fields_wf fields'
  end
) fields.

Fixpoint pow2 (x: nat) :=
  match x with
  | 0 => 1
  | S y => 2 * pow2 y
  end.

Fixpoint wf (t: Ty) : Prop :=
  valid_size (ty_size t)
  /\
  match t with
  | TInt size signedness => exists n, (pow2 n) = size
  | TBool => True
  | TPtr _ _ => True
  | TTuple fields size => fields_fit_size fields size
                      /\ fields_wf fields wf
                      /\ fields_disjoint fields
  | TArray elem_ty count => wf elem_ty
                        /\ (count >= 0)%Z
  | TUnion fields chunks size => fields_fit_size fields size
                             /\ fields_wf fields wf
                             /\ fields_in_chunks fields chunks
                             /\ chunks_disjoint chunks
                             /\ chunks_sorted chunks
                             /\ chunks_fit_size chunks size
  end.

End wf.