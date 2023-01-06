From Minirust.def Require Import defs encoding le wf.

Definition mono1 (ty: Ty) :=
  wf ty
  -> forall (v1 v2: Value),
  (le v1 v2)
  -> (is_valid_for ty v1)
  -> (is_valid_for ty v2)
  -> exists (v1_l v2_l: list AbstractByte),
  encode ty v1 = Some v1_l
  /\ encode ty v2 = Some v2_l
  /\ le v1_l v2_l.

Definition mono2 (ty: Ty) :=
  wf ty
  -> forall (l1 l2: list AbstractByte),
  (le l1 l2)
  -> le (decode ty l1) (decode ty l2).

Definition rt1 (ty: Ty) :=
  wf ty
  -> forall (v: Value),
  (is_valid_for ty v)
  -> exists (v_l: list AbstractByte),
  encode ty v = Some v_l
  /\ decode ty v_l = Some v.

Definition rt2 (ty: Ty) :=
  wf ty
  -> forall (l: list AbstractByte) (v: Value),
  (decode ty l = Some v)
  -> exists (v_l: list AbstractByte),
  encode ty v = Some v_l /\ le v_l l.