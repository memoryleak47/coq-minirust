From Minirust.def Require Import ty encoding utils thm wf.

Definition canonicalize ty l := decode ty l >>= encode ty.

Definition encode_len (ty: Ty) :=
  wf ty ->
  forall v, forall l,
  is_valid_for ty v ->
  encode ty v = Some l ->
  length l = ty_size ty.

(* will be extended by helper properties satisfied by all well-formed types *)
Record Props ty := {
  PR_RT1 : rt1 ty;
  PR_RT2 : rt2 ty;
  PR_MONO1 : mono1 ty;
  PR_MONO2 : mono2 ty;
  PR_ENCODE_LEN : encode_len ty
}.