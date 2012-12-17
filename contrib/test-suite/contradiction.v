
Lemma test_contradiction : Empty_set -> forall P,P.
intros.
contradiction.
Show Proof.
Qed.

Lemma test2 (P:Type) : P -> ~P -> forall Q,Q.
contradiction.
Show Proof.
Qed.

