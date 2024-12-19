
Definition pierre := forall (p q : Prop), ((p -> q) -> p) -> p.
Definition lem := forall (p : Prop),p \/ ~p.
Theorem eqn : lem <-> pierre.
Proof.
unfold pierre,lem.
split.
intros.
destruct (H p).
tauto.
tauto.
intros.
apply H with (q := ~(p \/ ~p)).
tauto.
Qed.