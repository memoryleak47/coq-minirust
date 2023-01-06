Lemma declare_impl {T: Type} (t: T) : exists t', t=t'. exists t. reflexivity. Qed.

Ltac declare x Hx obj := destruct (declare_impl obj) as [x Hx].
Ltac have x obj := destruct (declare_impl obj) as [x _].
