Add Rec LoadPath "../../theories" as HoTT.

Ltac with_conj P tac :=
  let f :=
    lazymatch type of (_:conjunction P _ _ _) with
    | conjunction _ ?andI ?andE1 ?andE2 =>
        (fun t => t andI andE1 andE2)
    end in
  f tac.
Ltac with_disj P tac :=
  lazymatch type of (_:disjunction P _ _ _) with
  | disjunction _ ?orI1 ?orI2 ?orE =>
      tac orI1 orI2 orE
  end.
Ltac with_iff P tac :=
  lazymatch type of (_:equivalence P _ _ _) with
  | equivalence _ ?iffI ?iffE1 ?iffE2 =>
      tac iffI iffE1 iffE2
  end.
(* Ugly: we should have a class for not as well... *)
Ltac is_not P :=
  let not_inst := constr:(_:propositional_logic _ _ P _ _ _ _) in
  idtac.

Ltac with_false P tac :=
  (* First find a logic *)
  let apl := constr:(@absurd_prop _ _) in
  (* and then match against P, to avoid P forcing the wrong sort *)
  lazymatch type of (_:apl P _) with
  | absurd_prop _ ?efq => tac efq
  end.
(*with_false Empty_set ltac:(fun h => assert (p:=h)).*)

Ltac with_true P tac :=
  (* First find a logic *)
  let tpl := constr:(@trivial_prop _ _) in
  (* and then match against P, to avoid P forcing the wrong sort *)
  lazymatch type of (_:tpl P _) with
  | trivial_prop _ ?I => tac I
  end.
(*with_true unit ltac:(fun h => assert (p:=h)).*)

Ltac with_unit_or_eq C tac :=
  with_true C tac ||
  lazymatch C with
  | ?R _ _ _ =>
      lazymatch type of (_:equational_logic R _ _ _ _ _) with
      | equational_logic _ _ ?refl _ _ _ => tac refl
      end
  end.
(*with_unit_or_eq (unit=unit) ltac:(fun h => generalize h).*)

Ltac flatten_contravariant_conj hyp typ c :=
  lazymatch typ with
  | ?C _ _ => with_conj C ltac:(fun andI andE1 andE2 =>
      generalize (fun x y => hyp (@andI _ _ x y)); intro;
      clear hyp)
  end.

Ltac flatten_contravariant_disj hyp typ c :=
  lazymatch typ with
  | ?C _ _ => with_disj C ltac:(fun orI1 orI2 _ =>
      generalize (fun x => hyp (@orI1 _ _ x)); intro;
      generalize (fun x => hyp (@orI2 _ _ x)); intro;
      clear hyp)
  end.

Ltac not_dep_intros :=
  repeat match goal with
  | |- (forall (_: ?X1), ?X2) => intro
  | |- (?C _) => is_not C; intro
  end.

Ltac axioms :=
  match reverse goal with
 | |- ?X1 => with_unit_or_eq X1 ltac:(fun rI => apply rI; fail)
 | id:?X1 |- _ =>
     with_false X1 ltac:(fun efq => elim id using efq)
 | _:?X1 |- ?X1 => assumption
 end.


Ltac simplif :=
  not_dep_intros;
  repeat
    (match reverse goal with
     | id: ?C _ _ |- _ => with_conj C ltac:(fun _ _ _ => destruct id)
     | id: (?C _ _) |- _ => with_iff C ltac:(fun iffI iffE1 iffE2 =>
        elim id; do 2 intro; clear id)
     | id: (?C _) |- _ =>is_not C; red in id
     | id: ?X1 _ _ |- _ =>
         with_disj X1 ltac:(fun _ _ orE => elim id using orE; clear id; intro)
     | id0: (forall (_: ?X1), ?X2), id1: ?X1|- _ =>
         (* generalize (id0 id1); intro; clear id0 does not work
            (see Marco Maggiesi's bug PR#301)
         so we instead use Assert and exact. *)
         assert X2; [exact (id0 id1) | clear id0]
     | id: forall (_ : ?X1), ?X2|- _ =>
         with_unit_or_eq X1 ltac:(fun rule =>
           cut X2;
	   [ intro; clear id
	   | (* id : forall (_: ?X1), ?X2 |- ?X2 *)
	     apply id; apply rule; fail])
     | id: forall (_ : ?X1), ?X2|- _ =>
        flatten_contravariant_conj id X1 X2
        (* moved from "id:(?A/\?B)->?X2|-" to "?A->?B->?X2|-" *)
     | id: forall (_: ?C ?X1 ?X2), ?X3|- _ =>
          with_iff C ltac:(fun iffI iffE1 iffE2 =>
            generalize (fun h1 h2 => id (@iffI _ _ h1 h2));
            clear id; intro)
     | id: forall (_:?X1), ?X2|- _ =>
          flatten_contravariant_disj id X1 X2
	  (* moved from "id:(?A\/?B)->?X2|-" to "?A->?X2,?B->?X2|-" *)
     | |- ?C _ _ => with_conj C ltac:(fun andI _ _ => apply andI)
     | |- ?C _ _ => with_iff C ltac:(fun iffI _ _ => apply iffI)
     | |- ?C _ => is_not C; intro
     end;
     not_dep_intros).


Ltac is_gen_impl X1 :=
  lazymatch X1 with
  | forall _, _ => idtac
  | ?C _ => is_not C
  end.


Ltac tauto_gen reduce solver :=
  let rec tauto_rec :=
    simplif;
    (axioms ||
    match reverse goal with
    | id:forall _:?X1, ?X3|- _ =>
        is_gen_impl X1;
        cut X3;
        [ intro; clear id; tauto_rec
        | apply id;
          generalize (fun x2 => id (fun _ => x2));
          clear id;
          solve [ tauto_rec ] ]
    | |- ?lor ?A ?B =>
        with_disj lor ltac:(fun orI1 orI2 orE =>
          solve [apply orI1; tauto_rec|apply orI2;tauto_rec])
    end ||
    (* NB: [|- _ -> _] matches any product *)
    match goal with
      | |- forall _,  _ => intro; tauto_rec
      | |- _  => reduce; solver
    end ||
    solver) in
  tauto_rec.

Ltac mytauto := tauto_gen idtac fail.
Ltac myintuition := tauto_gen idtac auto.


(**** Examples of intuitionistic tautologies ****)
Parameter A B C D E F : Type.
Parameter even : nat -> Type.
Parameter P : nat -> Type.

Lemma Ex_Wallen : (A -> B * C) -> (A -> B) + (A -> C).
Proof.
   mytauto.
Show Proof.
Qed.

Lemma Ex_Klenne : ~ ~ (A + ~ A).
Proof.
   mytauto.
Show Proof.
Qed.

Lemma Ex_Klenne' : forall n : nat, ~ ~ (even n + ~ even n).
Proof.
   mytauto.
Qed.

Lemma Ex_Klenne'' :
 ~ ~ ((forall n : nat, even n) + ~ (forall m : nat, even m)).
Proof.
   mytauto.
Qed.

Lemma tauto : (forall x : nat, P x) -> forall y : nat, P y.
Proof.
   mytauto.
Qed.

Lemma tauto1 : A -> A.
Proof.
   mytauto.
Qed.

Lemma tauto2 : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
   mytauto.
Qed.

Lemma a : forall (x0 : A + B) (x1 : B * C), A -> B.
Proof.
   mytauto.
Qed.

Lemma a2 : (A -> B * C) -> (A -> B) + (A -> C).
Proof.
   mytauto.
Qed.

Lemma a4 : ~ A -> ~ A.
Proof.
   mytauto.
Qed.

Lemma e2 : ~ ~ (A + ~ A).
Proof.
   mytauto.
Qed.

Lemma e4 : ~ ~ (A + B -> A + B).
Proof.
  mytauto.
Qed.

Lemma y0 :
 forall (x0 : A) (x1 : ~ A) (x2 : A -> B) (x3 : A + B) (x4 : A * B),
 A -> Empty_set.
Proof.
   mytauto.
Qed.

Lemma y1 : forall x0 : (A * B) * C, B.
Proof.
   mytauto.
Qed.

Lemma y2 : forall (x0 : A) (x1 : B), C + B.
Proof.
   mytauto.
Qed.

Lemma y3 : forall x0 : A * B, B * A.
Proof.
   mytauto.
Qed.

Lemma y5 : forall x0 : A + B, B + A.
Proof.
   mytauto.
Qed.

Lemma y6 : forall (x0 : A -> B) (x1 : A), B.
Proof.
   mytauto.
Qed.

Lemma y7 : forall (x0 : A * B -> C) (x1 : B) (x2 : A), C.
Proof.
   mytauto.
Qed.

Lemma y8 : forall (x0 : A + B -> C) (x1 : A), C.
Proof.
   mytauto.
Qed.

Lemma y9 : forall (x0 : A + B -> C) (x1 : B), C.
Proof.
   mytauto.
Qed.

Lemma y10 : forall (x0 : (A -> B) -> C) (x1 : B), C.
Proof.
   mytauto.
Qed.

(* This example took much time with the old version of Tauto *)
Lemma critical_example0 : (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.
Proof.
   mytauto.
Qed.

(* Same remark as previously *)
Lemma critical_example1 : (~ ~ B -> B) -> (~ B -> ~ A) -> ~ ~ A -> B.
Proof.
   mytauto.
Qed.

(* This example took very much time (about 3mn on a PIII 450MHz in bytecode)
   with the old Tauto. Now, it's immediate (less than 1s). *)
Lemma critical_example2 : (~ A <-> B) -> (~ B <-> A) -> (~ ~ A <-> A).
Proof.
   mytauto.
Qed.

(* This example was a bug *)
Lemma old_bug0 :
 (~ A <-> B) -> (~ (C + E) <-> D * F) -> (~ (C + A + E) <-> D * B * F).
Proof.
   mytauto.
Qed.

(* Another bug *)
Lemma old_bug1 : ((A -> B -> Empty_set) -> Empty_set) -> (B -> Empty_set) -> Empty_set.
Proof.
   mytauto.
Qed.

(* A bug again *)
Lemma old_bug2 :
 ((((C -> Empty_set) -> A) -> ((B -> Empty_set) -> A) -> Empty_set) -> Empty_set) ->
 (((C -> B -> Empty_set) -> Empty_set) -> Empty_set) -> ~ A -> A.
Proof.
   mytauto.
Qed.

(* A bug from CNF form *)
Lemma old_bug3 :
 (((~ A) + B) * ((~ B) + B) * ((~ A) + ~ B) * ((~ B) + ~ B) -> Empty_set) ->
 ~ ((A -> B) -> B) -> Empty_set.
Proof.
   mytauto.
Qed.


(* sometimes, the behaviour of Tauto depends on the order of the hyps *)
Lemma old_bug3bis :
 ~ ((A -> B) -> B) ->
 (((~ B) + ~ B) * ((~ B) + ~ A) * (B + ~ B) * (B + ~ A) -> Empty_set) -> Empty_set.
Proof.
   mytauto.
Qed.

(* A bug found by Freek Wiedijk <freek@cs.kun.nl> *)
Lemma new_bug :
 ((A <-> B) -> (B <-> C)) ->
 ((B <-> C) -> (C <-> A)) -> ((C <-> A) -> (A <-> B)) -> (A <-> B).
Proof.
   mytauto.
Qed.

(*  A private club has the following rules :
 *
 *  . rule 1 : Every non-scottish member wears red socks
 *  . rule 2 : Every member wears a kilt or doesn't wear red socks
 *  . rule 3 : The married members don't go out on sunday
 *  . rule 4 : A member goes out on sunday if and only if he is scottish
 *  . rule 5 : Every member who wears a kilt is scottish and married
 *  . rule 6 : Every scottish member wears a kilt
 *
 *  Actually, no one can be accepted !
 *)

Section club.

Variable Scottish RedSocks WearKilt Married GoOutSunday : Type.

Hypothesis rule1 : ~ Scottish -> RedSocks.
Hypothesis rule2 : WearKilt + ~ RedSocks.
Hypothesis rule3 : Married -> ~ GoOutSunday.
Hypothesis rule4 : GoOutSunday <-> Scottish.
Hypothesis rule5 : WearKilt -> Scottish * Married.
Hypothesis rule6 : Scottish -> WearKilt.

Lemma NoMember : Empty_set.
 mytauto.
Qed.

End club.

(**** Use of Intuition ****)
Lemma intu0 : nat ->
 (forall x : nat, P x) * B -> (forall y : nat, P y) * P 0 + B * P 0.
Proof.
myintuition.
Qed.

Require Import Paths.
Lemma intu1 :
 (forall A : Type, A + ~ A) -> forall x y : nat, (x = y) + (~ (x = y)).
Proof.
   myintuition.
Qed.
