From Minirust.def Require Import ty encoding utils thm wf.

Section defs.

Context {memory: Memory}.

Definition canonicalize ty l := decode ty l >>= encode ty.

Definition encode_len (ty: Ty) :=
  forall v, forall l,
  encode ty v = Some l ->
  length l = ty_size ty.

(* relevant properties satisfied by all well-formed types *)
Record Props ty := {
  PR_WF : wf ty;
  PR_RT1 : rt1 ty;
  PR_RT2 : rt2 ty;
  PR_MONO1 : mono1 ty;
  PR_MONO2 : mono2 ty;
  PR_ENCODE_LEN : encode_len ty
}.

End defs.