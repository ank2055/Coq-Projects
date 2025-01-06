Section a.
Variable p : Prop.
Theorem myth : p<-> p.
Proof.
split.
intros.
exact   H.
intros.
exact H.
Qed.
End a.

Section b.
Variable p q : Prop.
Theorem myth2 : p->q->p.
Proof.
intro.
intro.
exact H.
Qed.
End b.

Section c .
Variable p q r : Prop.
Theorem exercise : (p->q)->((q->r)->(p->r)).
Proof.
intros.
apply H0.
apply H.
exact H1.
Qed.

Theorem ex2 : (p->p->q)->p->q.
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

Theorem ex3 : (p->q->r) -> (p/\q)->r.
Proof.
intros.
destruct H0.
apply H.
assumption.
assumption.
Qed.
End c.

Section d.
Variable p q r s t : Prop.
Lemma d :(p->q)-> (p->r)->(q->r->t)->p->t.
Proof.
intros.
apply H1.
apply H.
assumption.
apply H0.
assumption.
Qed.
End d.

 



















