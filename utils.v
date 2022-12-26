Require Import Bool.
Require Import Datatypes.
Require Import Coq.Init.Byte.
Require Import ZArith.
Require Import List.
Import ListNotations.

Fixpoint transpose {T: Type} (l: list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | None::_ => None
  | (Some a)::rest =>
    let f := fun r => a::r in
    option_map f (transpose rest)
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

Fixpoint chunks_impl {T: Type} (tmp: list T) (chunk_size: nat) (l: list T) : list (list T) :=
  match (chunk_size =? length tmp,l) with
  | (_,[]) => [tmp]
  | (true,x::l') => tmp::(chunks_impl [x] chunk_size l')
  | (false,x::l') => chunks_impl (tmp ++ [x]) chunk_size l'
  end.

Definition chunks {T: Type} (l: list T) (chunk_size: nat) := chunks_impl [] chunk_size l.
