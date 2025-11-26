From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Class Eqb (A : Type) := {
  eqb : A -> A -> bool;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.

Notation "x =? y" := (eqb x y) (at level 70).

Instance Eqb_Nat : Eqb nat := {
  eqb := Nat.eqb;
  eqb_spec := Nat.eqb_spec
}.
