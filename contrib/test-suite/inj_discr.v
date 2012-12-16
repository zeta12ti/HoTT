(*Add Rec LoadPath "../../theories" as HoTT.*)
Require Import Paths.

Lemma discr : ~ 0 = 1.
discriminate.
Qed.

Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y.
injection p; trivial.
Qed.
Print inl_injective.
