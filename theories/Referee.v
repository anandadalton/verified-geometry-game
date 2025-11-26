Require Import Affine.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint scan_z (x y : Point) (zs : list Point) :=
  match zs with
  | [] => false
  | z :: zs' =>
    if algebraic_validb_points x y z
    then true
    else scan_z x y zs'
  end.

Fixpoint scan_y (x : Point) (ys : list Point) :=
  match ys with
  | [] => false
  | y :: ys' =>
    match scan_z x y ys' with
    | true => true
    | false => scan_y x ys'
    end
  end.

Fixpoint referee (xs : list Point) : bool :=
  match xs with
  | [] => false 
  | x :: xs' =>
    match scan_y x xs' with
    | true => true
    | false => referee xs'
    end
  end.

Inductive InPair (x y : Point) : list Point -> Prop :=
| Pair_Head : forall rest, In y rest -> InPair x y (x :: rest)
| Pair_Skip : forall h rest, InPair x y rest -> InPair x y (h :: rest).

Inductive InTriple (x y z : Point) : list Point -> Prop :=
| Triple_Head : forall rest, InPair y z rest -> InTriple x y z (x :: rest)
| Triple_Skip : forall h rest, InTriple x y z rest -> InTriple x y z (h :: rest).

Definition has_valid_triple (ls : list Point) : Prop :=
  exists x y z, InTriple x y z ls /\ algebraic_valid_points x y z.

Definition has_valid_triple_z (x y : Point) (zs : list Point) : Prop :=
  exists z, In z zs /\ algebraic_valid_points x y z.

(* By and large, the three reflection theorems we prove below proceed in exactly the same fashion. *)

Lemma reflect_has_valid_triple_z :
  forall x y zs, reflect (has_valid_triple_z x y zs) (scan_z x y zs).
Proof.
  intros x y zs. apply iff_reflect. split.
  - intros [z [Hin Hvalid]]. induction zs.
    + apply in_nil in Hin. contradiction.
    + destruct Hin as [Heq|Hin].
      * subst. rewrite (reflect_iff _ _ (reflect_algebraic_valid_points _ _ _)) in Hvalid.
        unfold scan_z. rewrite Hvalid. reflexivity.
      * apply IHzs in Hin. unfold scan_z. destruct (algebraic_validb_points x y a) eqn:Ha; [reflexivity|fold scan_z].
        apply Hin.
  - induction zs.
    + intro Habsurd. unfold scan_z in Habsurd. inversion Habsurd.
    + intro Hscan. destruct (algebraic_validb_points x y a) eqn:Hmatch.
      * exists a. rewrite <- (reflect_iff _ _ (reflect_algebraic_valid_points _ _ _)) in Hmatch.
        split; [apply in_eq|apply Hmatch].
      * unfold scan_z in Hscan. rewrite Hmatch in Hscan. fold scan_z in Hscan. apply IHzs in Hscan.
        destruct Hscan as [z [Hin Hvalid]]. exists z. split; [apply in_cons; apply Hin|apply Hvalid].
Qed.

Definition has_valid_triple_y (x : Point) (zs : list Point) : Prop :=
  exists y z, InPair y z zs /\ algebraic_valid_points x y z.

Lemma reflect_has_valid_triple_y :
  forall x zs, reflect (has_valid_triple_y x zs) (scan_y x zs).
Proof.
  intros x zs. apply iff_reflect. split.
  - intros [y [z [Hpair Hvalid]]].
    induction Hpair.
    + unfold scan_y. replace (scan_z x y rest) with true; [reflexivity|]. symmetry.
      rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_z _ _ _)).
      exists z. tauto.
    + unfold scan_y. destruct (scan_z x h rest) eqn:Hx; [reflexivity|]. fold scan_y. apply IHHpair.
  - induction zs.
    + intro Habsurd. unfold scan_y in Habsurd. inversion Habsurd.
    + unfold scan_y. destruct (scan_z x a zs) eqn:Hx.
      * intros _. rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_z _ _ _)) in Hx.
        destruct Hx as [z [Hin Hvalid]]. exists a, z. split; [apply Pair_Head; apply Hin|apply Hvalid].
      * fold scan_y. intros Hmatch. apply IHzs in Hmatch. destruct Hmatch as [y [z [Hpair Hvalid]]].
        exists y, z. split; [apply Pair_Skip; apply Hpair|apply Hvalid].
Qed.

Theorem reflect_has_valid_triple_referee :
  forall ls, reflect (has_valid_triple ls) (referee ls).
Proof.
  intros ls. apply iff_reflect. split.
  - intros [x [y [z [Htriple Hvalid]]]].
    induction Htriple.
    + unfold referee. replace (scan_y x rest) with true; [reflexivity|]. symmetry.
      rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_y _ _)).
      exists y, z. tauto.
    + unfold referee. destruct (scan_y h rest) eqn:Hy; [reflexivity|]. fold referee. apply IHHtriple.
  - induction ls.
    + intro Habsurd. unfold referee in Habsurd. inversion Habsurd.
    + unfold referee. destruct (scan_y a ls) eqn:Hy.
      * intros _. rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_y _ _)) in Hy.
        destruct Hy as [y [z [Hpair Hvalid]]]. exists a, y, z. split; [apply Triple_Head; apply Hpair|apply Hvalid].
      * fold referee. intros Hmatch. apply IHls in Hmatch. destruct Hmatch as [x [y [z [Htriple Hvalid]]]].
        exists x, y, z. split; [apply Triple_Skip; apply Htriple|apply Hvalid].
Qed.