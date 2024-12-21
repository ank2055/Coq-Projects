Definition lem := forall (p : Prop),p \/~p.
Theorem forbenius (A: Set)(p : A -> Prop)(q: Prop) :
(lem /\(forall x : A,q \/ p x))<->(q \/ forall x :A, p x)/\(lem).
Proof.
split.
unfold lem.
intros.
destruct H .
assert (G := (H q)).
destruct G.
tauto.
firstorder.
split.
destruct H.
assumption.
destruct H.
destruct H .
tauto.
firstorder.
Qed.
Check forbenius.
Print forbenius.