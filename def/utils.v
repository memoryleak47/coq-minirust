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

Fixpoint subslice_with_length {T: Type} (l: list T) (start: nat) (length: nat) : list T :=
  match (l,start,length) with
  | (_::l', S start', ln) => subslice_with_length l' start' ln
  | (x::l', 0, S ln') => x::(subslice_with_length l' 0 ln')
  | (_, 0, 0) => []
  | ([],_,_) => []
  end.

Fixpoint write_subslice_at_index {T: Type} (l: list T) (start: nat) (other: list T) : list T :=
  match (l,start,other) with
  | (x::l', S start', o) => x::(write_subslice_at_index l' start' o)
  | (_::l', 0, y::o') => y::(write_subslice_at_index l' 0 o')
  | (l, 0, []) => l
  | ([],_,_) => []
  end.

Definition assuming {T: Type} (f: T -> bool) (t: T)  :=
  if f t then Some t else None.

Definition assuming_const {T: Type} (b: bool) (t: T)  :=
  if b then Some t else None.

Fixpoint chunks_impl {T: Type} (gas: nat) (l: list T) (chunk_size: nat) :=
  match gas with
  | 0 => []
  | S gas' =>
    match firstn chunk_size l with
    | [] => []
    | x => x::(chunks_impl gas' (skipn chunk_size l) chunk_size)
    end
  end.

Definition chunks {T: Type} (l: list T) (chunk_size: nat) :=
  chunks_impl (length l) l chunk_size.
