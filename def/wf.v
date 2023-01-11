Require Import ZArith List Permutation.
Import ListNotations.
From Minirust.def Require Import ty int_encoding.

Section wf.

Context {params: Params}.

Definition valid_size (size: Size) : Prop := (int_in_range (Z.of_nat size) PTR_SIZE Signed) = true.

Definition fields_fit_size (fields: Fields) (size : Size) :=
let f := (fun field =>
  let start := fst field in
  let ty := snd field in
  let stop := start + ty_size ty in

  size >= stop
) in Forall f fields.

Definition chunks_fit_size (chunks: Chunks) (size: Size) :=
let f := (fun chunk =>
  let start := fst chunk in
  let len := snd chunk in
  let stop := start + len in

  size >= stop
) in Forall f chunks.

Definition fields_wf (fields: Fields) (wf_call: Ty -> Prop) :=
(fix fields_wf (fields: Fields) :=
  match fields with
  | [] => True
  | (_, ty)::fields' => wf_call ty /\ fields_wf fields'
  end
) fields.

(* an interval is (offset, size) in bytes *)
Notation Interval := (Size * Size)%type.

(* checks whether i1 stops before i2 starts *)
Definition interval_pair_sorted_disjoint (i1 i2: Interval) :=
  match (i1,i2) with
  | ((o1,s1), (o2,s2)) => o1+s1 <= o2
  end.

(* checks whether i1 is fully contained in i2 *)
Definition interval_pair_contained_in (i1 i2: Interval) :=
  match (i1,i2) with
  | ((o1,s1), (o2,s2)) => o2 <= o1 /\ o2+s2 >= o1+s2
  end.

(* checks that the intervals are sorted, and don't overlap *)
Definition intervals_sorted_disjoint (l: list Interval) :=
  ForallOrdPairs interval_pair_sorted_disjoint l.

Definition intervals_disjoint (l: list Interval) := exists l' (_: Permutation l l'), intervals_sorted_disjoint l'.

Definition interval_of_field (f: Size * Ty) :=
  match f with
  | (o,t) => (o, ty_size t)
  end.

Definition fields_disjoint (fields: Fields) : Prop :=
  intervals_disjoint (map interval_of_field fields).

(* checks that every field is completely contained a chunk *)
(* note that a chunk is already an `Interval` *)
Definition fields_in_chunks (fields: Fields) (chunks: Chunks) :=
  let fn := (fun f c => interval_pair_contained_in (interval_of_field f) c) in
  Forall (fun f => Exists (fun c => fn f c) chunks) fields.

Definition chunks_sorted_and_disjoint (chunks: Chunks) := intervals_sorted_disjoint chunks.

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
                             /\ chunks_sorted_and_disjoint chunks
                             /\ chunks_fit_size chunks size
  end.

End wf.