(* Bits an pieces from Coq's Init/Datatypes.v *)

Declare ML Module "nat_syntax_plugin".

(* Natural numbers. *)

Inductive nat : Set :=
  | O
  | S (_:nat).

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Arguments S _.

Open Scope nat_scope. (* Originally in Peano.v *)
