Require Import defs encoding thm lemma utils wf.
Require Import Coq.Init.Byte.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import NArith.
Require Import List.
Import ListNotations.
Require Import Ndigits.
Require Import ZArith.

Section array.

Context (elem_ty: Ty).
Context (count: Int).

Notation t := (TArray elem_ty count).

Lemma bind_some {T T'} {x: T} {f: T -> option T'} : (Some x >>= f) = f x.
Proof.
simpl. auto.
Qed.

Lemma transpose_map {T1 T2 T3} {f: T1 -> option T2} {g: T2 -> option T3} {l: list T1} {l'} (H: transpose (map f l) = Some l') :
map g l' = map (fun x => (f x) >>= g) l.
Proof.
Admitted.

Lemma transpose_some {T} {x: T} {l: list (option T)} : transpose ((Some x) :: l) = (transpose l o-> (fun a => x :: a)).
Admitted.

Lemma array_encode_none {v} (H: encode t v = None) : ~is_valid_for t v.
Proof.
Admitted.

Lemma encode_len {v ty l} (H: encode t v = Some l) : length l = ty_size ty.
Proof.
Admitted.

Lemma chunks_concat {T} {s} {l : list (list T)} (H: Forall (fun x => length x = s) l) :
  utils.chunks (concat l) s = l.
Proof.
Admitted.

Lemma array_rt1 : rt1 t.
Proof.
intros Hwf v Hval.
destruct (encode t v) as [l|] eqn:Henc; cycle 1. {
  exfalso.
  apply (array_encode_none Henc).
  assumption.
}

exists l.
split. { auto. }

assert (exists vs, v = VTuple vs). {
  unfold encode,encode_array in Henc.
  destruct v; try (simpl in Henc; discriminate Henc).
  eexists _. auto.
}
inversion H as [vs ->]. clear H.
unfold decode. fold decode.
unfold decode_array.
simpl in Henc.
unfold encode_array in Henc.
simpl in Henc.
unfold utils.assuming in Henc.

destruct (BinInt.Z.eqb (BinInt.Z.of_nat (length vs)) count); cycle 1.
{ simpl in Henc. discriminate Henc. }

simpl in Henc.
unfold utils.opt_bind in Henc.

match goal with
| _ : (utils.opt_map _ ?transp = Some _) |- _ => destruct transp eqn:Htransp
end; cycle 1.
{ simpl in Henc. discriminate Henc. }
 
simpl in Henc. inversion Henc. clear Henc H0 l.

rewrite chunks_concat; cycle 1. { admit. }
rewrite (transpose_map Htransp).

assert (forall x l, encode elem_ty x = Some l -> (length l =? ty_size elem_ty) = true). { admit. }

match goal with
| |- (transpose (map ?f _) o-> _) = _ => replace f with (fun x => encode elem_ty x >>= decode elem_ty)
end; cycle 1. {
  apply functional_extensionality_dep.
  intros v.
  destruct (encode elem_ty v) eqn:E.
  - rewrite (H v). auto. assumption.
  - auto.
}

assert (transpose (map
 (fun x : Value => encode elem_ty x >>= decode elem_ty) vs) = Some vs); cycle 1.
{ rewrite H0. simpl. auto. }

generalize dependent l0.
induction vs as [|v vs' IH].
{ admit. }

intros l0 Htransp.
rewrite map_cons.

assert (is_valid_for elem_ty v). { admit. }
assert (Hwf': wf elem_ty). { admit. }

destruct (encode elem_ty v) eqn:E; cycle 1. {
  simpl in Htransp.
  rewrite E in Htransp.
  discriminate Htransp.
}

assert (Hrt1 : rt1 elem_ty). { admit. }
destruct (Hrt1 Hwf' v H0) as [ll [Henc Hdec]].
assert (Hrew: ll = l). { rewrite Henc in E. inversion E. auto. }
rewrite Hrew in Hdec,Henc. clear Hrew ll.
rewrite bind_some.
rewrite Hdec.
rewrite transpose_some.

destruct l0.
{ (* discriminate within Htransp, left-side has length > 0, while right-side is []. *) admit. }

(* TODO this doesn't hold! We just need a way to get is_valid_for elem_ty for all elements of vs. *)
assert (is_valid_for t (VTuple vs')). { admit. }

rewrite (IH H1 l1).
- simpl. auto.
- (* consequence of Htransp *) admit.
Admitted.

Lemma array_rt2 : rt2 t.
Proof.
Admitted.

Lemma array_mono1 : mono1 t.
Proof.
Admitted.

Lemma array_mono2 : mono2 t.
Proof.
Admitted.

End array.