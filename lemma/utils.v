Require Import List.
From Minirust.def Require Import utils.

Lemma declare_impl {T: Type} (t: T) : exists t', t=t'. exists t. reflexivity. Qed.

Ltac declare x Hx obj := destruct (declare_impl obj) as [x Hx].
Ltac have x obj := destruct (declare_impl obj) as [x _].

Lemma bind_some {T T'} {x: T} {f: T -> option T'} : (Some x >>= f) = f x.
Proof.
simpl. auto.
Qed.

Lemma bind_none {T T'} {f: T -> option T'} : (None >>= f) = None.
Proof.
simpl. auto.
Qed.

Lemma transpose_map {T1 T2 T3} {f: T1 -> option T2} {g: T2 -> option T3} {l: list T1} {l'} (H: transpose (map f l) = Some l') :
map g l' = map (fun x => (f x) >>= g) l.
Proof.
Admitted.

Lemma transpose_some {T} {x: T} {l: list (option T)} : transpose ((Some x) :: l) = (transpose l o-> (fun a => x :: a)).
Admitted.