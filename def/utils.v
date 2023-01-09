Require Import Bool Datatypes Coq.Init.Byte ZArith List.
Import ListNotations.

Definition opt_bind {aT rT : Type} (f: aT -> option rT) (o: option aT):  option rT :=
  match o with
  | Some a => f a
  | None => None
  end.

Definition opt_map {aT rT : Type} (f: aT -> rT) (o: option aT):  option rT :=
  match o with
  | Some a => Some (f a)
  | None => None
  end.

Notation "x >>= f" := (opt_bind f x) (at level 70).
Notation "x o-> f" := (opt_map f x) (at level 70).

Fixpoint transpose {T: Type} (l: list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | None::_ => None
  | (Some a)::l' => (transpose l') o-> (fun r => a::r)
  end.

Definition subslice_with_length {T: Type} (l: list T) (start: nat) (length: nat) : list T :=
  firstn length (skipn start l).

Definition write_subslice_at_index {T: Type} (l: list T) (start: nat) (other: list T) : list T :=
  (firstn start l) ++ other ++ skipn (start + length other) l.

Definition assuming {T: Type} (f: T -> bool) (t: T)  :=
  if f t then Some t else None.

Definition assuming_const {T: Type} (b: bool) (t: T)  :=
  if b then Some t else None.