Require Import defs encoding thm lemma wf int_encoding high low le.
Require Import Coq.Init.Byte.
Require Import List.
Require Import ZArith.
Import ListNotations.

Section ptr.

Context (layout: Layout).

Notation align := (
  match layout with
  | mkLayout align size => align
  end).

Notation size := (
  match layout with
  | mkLayout align size => size
  end).

Context (ptr_ty: PtrTy).

Notation t := (TPtr ptr_ty layout).

Notation Constraints addr align := (
  match ptr_ty with
  | Raw => true
  | Ref => ((addr >? 0)%Z && (addr mod (Z.of_nat align) =? 0)%Z)%bool
  end).

Inductive ValidPtr : Value -> Type :=
  | mkValidPtr addr p : Constraints addr align = true -> ValidPtr (VPtr addr p).

Lemma valid_ptr (v: Value) (H: is_valid_for t v) :
  ValidPtr v.
Proof.

unfold is_valid_for in H.
Admitted.

Lemma ptr_mono1 : mono1 t.
Proof.
intros Hwf v1 v2 Hle Hv1 Hv2.
assert (exists a b, VPtr a b = v1). {
  destruct Hv1. unfold decode,decode_ptr in H.
  destruct (unwrap_abstract x); cycle 1. { discriminate H. }
  simpl in H.
  destruct (decode_int_raw PTR_SIZE Unsigned l); cycle 1. { discriminate H. }
  simpl in H.
  unfold utils.assuming in H. simpl in H.
  destruct (Constraints i align) eqn:E; cycle 1. { discriminate H. }
  simpl in H.
  injection H.
  intros L.
  (* TODO better solution? *)
  exists i. exists ((ssrfun.Option.bind
          (utils.assuming_const
             (forallb
                (fun x0 : AbstractByte =>
                 match x0 with
                 | Uninit => false
                 | Init _ (Some a) =>
                     match
                       match x with
                       | Init _ p0 :: _ => p0
                       | _ => None
                       end
                     with
                     | Some b0 => P_EQ a b0
                     | None => false
                     end
                 | Init _ None =>
                     match
                       match x with
                       | Init _ p0 :: _ => p0
                       | _ => None
                       end
                     with
                     | Some _ => false
                     | None => true
                     end
                 end) x))
          match x with
          | Init _ p :: _ => p
          | _ => None
          end)). auto.
}
destruct H as [addr].
destruct H as [p Hv].
rewrite <- Hv.
rewrite <- Hv in Hle.
Admitted.

Lemma ptr_mono2 : mono2 t.
Proof.
Admitted.

Lemma ptr_rt1 : rt1 t.
Proof.
intros _ v Hval.
Admitted.

Lemma ptr_rt2 : rt2 t.
Proof.
Admitted.

End ptr.