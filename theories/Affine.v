From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Eqb.

Inductive F3 : Type := F0 | F1 | F2.

Definition add (a b : F3) : F3 :=
  match a, b with
  | F0, x => x
  | x, F0 => x
  | F1, F1 => F2
  | F1, F2 => F0
  | F2, F1 => F0
  | F2, F2 => F1
  end.

Notation "a + b" := (add a b) (at level 50, left associativity).

Definition eqb_F3 (x y : F3) : bool :=
  match x, y with
  | F0, F0 => true | F1, F1 => true | F2, F2 => true | _, _ => false
  end.

Lemma eqb_F3_spec : forall x y : F3, reflect (x = y) (eqb_F3 x y).
Proof.
 intros x y. apply iff_reflect.
 destruct x, y; simpl; split; auto; discriminate.
Qed.

Instance Eqb_F3 : Eqb F3 := {
  eqb := eqb_F3;
  eqb_spec := eqb_F3_spec
}.

Record Point : Type := mkPoint {
  d1 : F3; d2 : F3; d3 : F3; d4 : F3
}.

Definition eqb_Point (p1 p2 : Point) : bool :=
  (d1 p1 =? d1 p2) &&
  (d2 p1 =? d2 p2) &&
  (d3 p1 =? d3 p2) &&
  (d4 p1 =? d4 p2).

Lemma eqb_Point_spec : forall p1 p2 : Point, reflect (p1 = p2) (eqb_Point p1 p2).
Proof.
  intros p1 p2.
  apply iff_reflect.
  unfold eqb_Point.
  (* Note: this next step doesn't result in case analysis; it just makes
     explicit the components of p1 and p2. *)
  destruct p1, p2; simpl.
  repeat rewrite andb_true_iff.
  (* The next step transforms eqb_F3 into =.*)
  repeat rewrite <- (reflect_iff _ _ (eqb_F3_spec _ _)).
  
  split; intro H.
  - (* Forward: Prove if the points are equal, the components are. *)
    inversion H. tauto.
  - (* Reverse: Prove if the components are equal, the points are. *)
    (* First we need to peel apart that conjucted hypothesis. *)
    destruct H as [[[H1 H2] H3] H4].
    subst. reflexivity.
Qed.

Instance Eqb_Point : Eqb Point := {
  eqb := eqb_Point;
  eqb_spec := eqb_Point_spec
}.

Lemma reflect_negb : forall (P : Prop) (b : bool),
  reflect P b -> (negb b = true <-> ~P).
Proof.
  intros P b H. destruct H; simpl; split; auto; discriminate.
Qed.

(* "Intuitive" Definitions of a Valid triple in F3. *)
Definition intuitive_validb (a b c : F3) : bool :=
 ((a =? b) && (b =? c)) || (negb (a =? b) && negb (b =? c) && negb (a =? c)).

Definition intuitive_valid (a b c : F3) : Prop :=
 (a = b /\ b = c) \/ (a <> b /\ b <> c /\ a <> c).

Lemma reflect_intuitive_valid : forall (x y z : F3),
  reflect (intuitive_valid x y z) (intuitive_validb x y z).
Proof.
  intros x y z.
  apply iff_reflect.
  unfold intuitive_validb.
  unfold intuitive_valid.
  simpl.
  (* The next bit is just corralling all our bool logic to Prop. *)
  rewrite orb_true_iff.
  repeat rewrite andb_true_iff.
  repeat rewrite (reflect_negb _ _ (eqb_F3_spec _ _)).
  repeat rewrite <- (reflect_iff _ _ (eqb_F3_spec _ _)).
  tauto.
Qed.

(* "Algebraic" Definitions of a Valid triple in F3. *)

Definition algebraic_validb (a b c : F3) : bool :=
 a + b + c =? F0.

Definition algebraic_valid (a b c : F3) : Prop :=
 a + b + c = F0.

(* This just follows almost immediately from reflecting F3 equality. *)
Lemma reflect_algebraic_valid : forall (x y z : F3),
  reflect (algebraic_valid x y z) (algebraic_validb x y z).
Proof.
  intros x y z.
  apply iff_reflect.
  unfold algebraic_validb.
  unfold algebraic_valid.
  rewrite <- (reflect_iff _ _ (eqb_F3_spec _ _)).
  tauto.
Qed.

(* A bridge between intuitive_valid and algebraic_valid is what we want,
   but doing this in Bool first is easier. This is brute-force 27 cases,
   which is bad; but the proof is very simple, which is good. *)

Lemma intuitive_validb_algebraic_validb_equiv : forall (x y z : F3),
  algebraic_validb x y z = intuitive_validb x y z.
Proof.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

(* Finally, the centerpiece. *)
Theorem intuitive_valid_algebraic_valid_equiv : forall (x y z : F3),
  algebraic_valid x y z <-> intuitive_valid x y z.
Proof.
  intros x y z.
  rewrite (reflect_iff (algebraic_valid x y z) (algebraic_validb x y z) (reflect_algebraic_valid _ _ _)).
  rewrite (reflect_iff (intuitive_valid x y z) (intuitive_validb x y z) (reflect_intuitive_valid _ _ _)).
  rewrite intuitive_validb_algebraic_validb_equiv.
  tauto.
Qed.

(* The algebraic definition of a valid triple of points ("a set") *)
Definition algebraic_validb_points (x y z : Point) : bool :=
  algebraic_validb (d1 x) (d1 y) (d1 z) &&
  algebraic_validb (d2 x) (d2 y) (d2 z) &&
  algebraic_validb (d3 x) (d3 y) (d3 z) &&
  algebraic_validb (d4 x) (d4 y) (d4 z).

Definition algebraic_valid_points (x y z : Point) : Prop :=
  algebraic_valid (d1 x) (d1 y) (d1 z) /\
  algebraic_valid (d2 x) (d2 y) (d2 z) /\
  algebraic_valid (d3 x) (d3 y) (d3 z) /\
  algebraic_valid (d4 x) (d4 y) (d4 z).

Theorem reflect_algebraic_valid_points : forall (x y z : Point),
  reflect (algebraic_valid_points x y z) (algebraic_validb_points x y z).
Proof.
  intros x y z.
  apply iff_reflect.
  unfold algebraic_validb_points.
  unfold algebraic_valid_points.
  repeat rewrite andb_true_iff.
  repeat rewrite (reflect_iff (algebraic_valid _ _ _) (algebraic_validb _ _ _) (reflect_algebraic_valid _ _ _)).
  tauto.
Qed.
