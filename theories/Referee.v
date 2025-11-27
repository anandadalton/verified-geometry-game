Require Import Affine.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Fixpoint scan_z (x y : Point) (ls : list Point) :=
  match ls with
  | [] => false
  | z :: ls' =>
    if algebraic_validb_points x y z
    then true
    else scan_z x y ls'
  end.

Fixpoint scan_y (x : Point) (ls : list Point) :=
  match ls with
  | [] => false
  | y :: ls' =>
    match scan_z x y ls' with
    | true => true
    | false => scan_y x ls'
    end
  end.

Fixpoint referee (ls : list Point) : bool :=
  match ls with
  | [] => false 
  | x :: ls' =>
    match scan_y x ls' with
    | true => true
    | false => referee ls'
    end
  end.

(* Semantically, x and y appear in ls in that order (not necessarily
   continguously. *)
Inductive InPair (x y : Point) : list Point -> Prop :=
| Pair_Head : forall ls, In y ls -> InPair x y (x :: ls)
| Pair_Skip : forall h ls, InPair x y ls -> InPair x y (h :: ls).

(* Same as InPair, but x, y, and z appear in ls in that order. *)
Inductive InTriple (x y z : Point) : list Point -> Prop :=
| Triple_Head : forall ls, InPair y z ls -> InTriple x y z (x :: ls)
| Triple_Skip : forall h ls, InTriple x y z ls -> InTriple x y z (h :: ls).

(* Algebraic definition of having a valid triple.
   Notice that InTriple has the advantage of guaranteeing the selection of
   _distinct_ points from our list. Otherwise, for a nonempty list h :: ls,
   it is trivially the case that algebraic_valid_points h h h. *)
Definition has_valid_triple (ls : list Point) : Prop :=
  exists x y z, InTriple x y z ls /\ algebraic_valid_points x y z.

(* Our end goal is to prove that `reflect has_valid_triple referee`, but this
   is initially too difficult. So instead we come up with some propositions
   that reflect scan_z and scan_y. This is the reflection in Prop of scan_z. *)
Definition has_valid_triple_z (x y : Point) (zs : list Point) : Prop :=
  exists z, In z zs /\ algebraic_valid_points x y z.

(* This is the reflection in Prop of scan_y. *)
Definition has_valid_triple_y (x : Point) (zs : list Point) : Prop :=
  exists y z, InPair y z zs /\ algebraic_valid_points x y z.

(* By and large, the three reflection theorems we prove below proceed in
   exactly the same fashion. I tried to keep to some conventions:
   - Hvalid is a witness that some triple is valid.
   - Hmatch means one of our fixpoints found a witness. *)
Lemma reflect_has_valid_triple_z :
  forall x y ls, reflect (has_valid_triple_z x y ls) (scan_z x y ls).
Proof.
  intros x y ls. apply iff_reflect. split.
  - (* Forward: has_valid_triple_z x y zs -> scan_z x y zs. *)
    intros [z [Hin Hvalid]]. induction ls as [|h ls' IH].
    + contradiction (in_nil Hin).
    + (* Either z is the head of the list or it is not. *)
      destruct Hin as [Heq|Hin]. 
      * (* If it _is_ the head then we can reflect Hmatch into bool and then
           evaluate scan_z directly. *)
        subst.
        rewrite (reflect_iff _ _ (reflect_algebraic_valid_points _ _ _)) in Hvalid.
        unfold scan_z.
        rewrite Hvalid. reflexivity.
      * (* If z is in the tail, we can use the inductive hypothesis. *)
        simpl. rewrite (IH Hin).
        destruct (algebraic_validb_points x y h); reflexivity.
  - (* Backward: scan_z x y zs -> has_valid_triple_z x y zs *)
    induction ls as [|h ls' IH].
    + intro Habsurd. simpl in Habsurd. inversion Habsurd.
    + intro Hmatch. simpl in Hmatch.
      destruct (algebraic_validb_points x y h) eqn:Hvalid.
      * (* (x, y, h) works allows us to explicitly construct a proof of has_valid_triple. *)
        exists h. rewrite <- (reflect_iff _ _ (reflect_algebraic_valid_points _ _ _)) in Hvalid.
        split; [apply in_eq|apply Hvalid].
      * simpl in Hmatch. apply IH in Hmatch.
        destruct Hmatch as [z [Hin Hvalid']]. exists z.
        split; [apply in_cons; apply Hin|apply Hvalid']. 
Qed.

Lemma reflect_has_valid_triple_y :
  forall x ls, reflect (has_valid_triple_y x ls) (scan_y x ls). 
Proof.
  intros x ls. apply iff_reflect. split.
  - intros [y [z [Hpair Hvalid]]].  induction Hpair as [ls' Hin| h ls' Hin Hpair].
    + unfold scan_y. replace (scan_z x y ls') with true; [reflexivity|]. symmetry.
      rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_z _ _ _)).
      exists z. split; [apply Hin|apply Hvalid].
    + unfold scan_y. destruct (scan_z x h ls') eqn:Hmatch; [reflexivity|].  fold scan_y. apply Hpair.
  - induction ls as [|h ls' IH].
    + intro Habsurd. unfold scan_y in Habsurd. discriminate. 
    + (* We can find a z such that (x, h, z) works or we can't. *)
      unfold scan_y. destruct (scan_z x h ls') eqn:Hmatch.
      * (* There is such a z; use reflection to exhibit it explicitly. *)
        intros _. rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_z _ _ _)) in Hmatch.
        (* This next bit is just cobbling together has_valid_triple_y out of has_valid_triple_z. *)
        destruct Hmatch as [z [Hin Hvalid]]. exists h, z.
        split; [apply Pair_Head; apply Hin|apply Hvalid].
      * (* We know that h doesn't work but some triple (x, y, z) does, with y, z in the tail.
           Our induction hypothesis lets us reflect in this case and explicitly exhibit the triple. *)
        fold scan_y. intros Hmatch'. apply IH in Hmatch'.
        (* Disassembling has_valid_triple_y to make a new instance (but now ls' is extended by h). *) 
        destruct Hmatch' as [y [z [Hpair Hvalid]]]. exists y, z.
        split; [apply Pair_Skip; apply Hpair|apply Hvalid].
Qed.

(* Because our referee returns true if and only if there is a valid triple in
   the list, we can be confident when we use it to determine whether to deal
   out cards or not. *)

Theorem reflect_has_valid_triple_referee :
  forall ls, reflect (has_valid_triple ls) (referee ls). 
Proof.
  intros ls.  apply iff_reflect. split. 
  - intros [x [y [z [Htriple Hvalid]]]]. induction Htriple as [ls' Hhead|h ls' Htriple IH]. 
    + unfold referee.
      (* Because we know by induction that InPair y z ls', and we know that (x y z)
         is a witness, it should definitely be true that scan_y x ls' is true; we
         just need to prove it. *)
      replace (scan_y x ls') with true; [reflexivity|]. symmetry.
      rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_y _ _)).
      exists y, z. split; [apply Hhead|apply Hvalid].
    + unfold referee.
      (* If scan_y h ls' = true we are done automatically, otherwise we just need to employ our
         inductive hypothesis. *)
      destruct (scan_y h ls') eqn:Hmatch; [reflexivity|]. fold referee. apply IH.
  - induction ls as [|h ls' IH].
    + intro Habsurd. unfold referee in Habsurd. discriminate. 
    + unfold referee. destruct (scan_y h ls') eqn:Hmatch.
      * (* If scan_y h ls', then the head of the list is the first element of our witness;
           and we can extract this witness using reflection. *)
        intros _.  rewrite <- (reflect_iff _ _ (reflect_has_valid_triple_y _ _)) in Hmatch.
        (* Now to cobble has_valid_triple from has_valid_triple_y. *)
        destruct Hmatch as [y [z [Hpair Hvalid]]]. exists h, y, z.
        split; [apply Triple_Head; apply Hpair|apply Hvalid].
      * (* Since h didn't work, we just use IH. *)
        fold referee. intros Hmatch'. apply IH in Hmatch'. destruct Hmatch' as [x [y [z [Htriple Hvalid]]]].
        exists x, y, z. split; [apply Triple_Skip; apply Htriple|apply Hvalid].
Qed.