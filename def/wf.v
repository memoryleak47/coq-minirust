Require Import ZArith List.
Import ListNotations.

From Minirust.def Require Import defs int_encoding.

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

Definition fields_disjoint (fields: Fields) : Prop.
Admitted.

(* checks that every field is completely contained a chunk *)
Definition fields_in_chunks (fields: Fields) (chunks: Chunks) : Prop.
Admitted.

Definition chunks_sorted_and_disjoint (chunks: Chunks) : Prop.
Admitted.

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