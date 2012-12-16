(* Bits an pieces from Coq's Init/Datatypes.v *)

Require Export Notations.
Require Import LogicClasses.
Global Set Universe Polymorphism.

(** Building the logic in Type *)

(** Universe polymorphism gives us a hard time. For whatever reason,
    it insists on instantiating the class instance declarations in
    X:=Set, even when we explicitly give Type. Generating a
    monomorphic universe [logic_universe] prevents this.
    This does not impair the possibility to have the logic
    connectives at various levels, as they are defined as polymorphic.
    The class mechanism is just there to tag the connectives.
*)
Monomorphic Definition logic_universe := Type.
Global Instance log_Type : logic_kind logic_universe :=
  fun X => X.

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B: Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Scheme sum_elim := Minimality for sum Sort Type.

Global Instance log_disj : disjunction sum (@inl) (@inr) sum_elim.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst {A B : Type} (p : A * B) := match p with (x, y) => x end.
Definition snd {A B : Type} (p : A * B) := match p with (x, y) => y end.

Hint Resolve pair inl inr : core.

Global Instance log_conj : conjunction prod (@pair) (@fst) (@snd).

(** [iff A B], written [A <-> B], is the logical equivalence of
    [A] and [B]; the introduction rule is mkIff, and the projections
    are iffLR and iffRL, to derive implications in both directions. *)
Record iff (A B : Type) := mkIff {
  iffLR : A -> B;
  iffRL : B -> A
}.

Notation "A <-> B" := (iff A B).

Global Instance log_iff : equivalence iff mkIff iffLR iffRL.


(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type. *)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x : A, P x -> sigT P.

Arguments sigT (A P)%type.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Add Printing Let sigT.

Definition projT1 {A : Type} {P : A -> Type} (x : sigT P) : A :=
  match x with | existT a _ => a end.

Definition projT2 {A : Type} {P : A -> Type} (x : sigT P) : P (projT1 x) :=
  match x return P (projT1 x) with | existT _ h => h end.

Scheme sigT_elim := Minimality for sigT Sort Type.

Global Instance log_fol : first_order_logic (@sigT) (@existT) sigT_elim.


(** [Empty_set] is a datatype with no inhabitant *)

Inductive Empty_set : Set :=.

Scheme Empty_set_elim := Minimality for Empty_set Sort Type.

(** We have to be careful here because the inferred type for
    Empty_set is not Type *)
Global Instance log_absurd :
  absurd_prop (L:=log_Type) Empty_set Empty_set_elim.

Definition not (A:Type) : Type := A -> Empty_set.

Notation "~ A" := (not A).

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.

Global Instance log_true : trivial_prop (L:=log_Type) unit tt.

Global Instance log_propositional :
  propositional_logic log_conj log_disj not log_iff log_true log_absurd Set.

Global Instance log_full :
  full_logic (X:=Type) log_propositional log_fol.
