Require Import Eqb Affine.
From Stdlib Require Import List Bool.
Import ListNotations.

Definition all_f3 : list F3 := [F0; F1; F2].

Definition entire_deck : list Point :=
  flat_map (fun d1 =>
    flat_map (fun d2 =>
      flat_map (fun d3 =>
        map (fun d4 =>
          mkPoint d1 d2 d3 d4
        ) all_f3
      ) all_f3
    ) all_f3
  ) all_f3.

(* Verification of some properties of Deck.
   Personally I think we probably don't need these to prove that our game
   engine is well-behaved, but maybe they'll come in handy, and it's fun. *)

Theorem deck_size_81 : length entire_deck = 81.
Proof.
  reflexivity.
Qed.

Fixpoint linear_card_search (x : Point) (ls : list Point) : bool :=
  match ls with
  | [] => false
  | (h :: ls') => if x =? h then true else linear_card_search x ls'
  end.

(* This makes the proof of deck_complete smoother. *)
Lemma reflect_linear_card_search : forall (x : Point) (ls : list Point),
  reflect (In x ls) (linear_card_search x ls).
Proof.
  induction ls as [|h ls' IH].
  - simpl. apply ReflectF. tauto.
  - apply iff_reflect. split.
    + (* Forward: In x (h :: ls') -> linear_card_search x (h :: ls') = true. *)
      intro Hin. destruct Hin as [Heq | Hin'].
      * subst. simpl. rewrite eqb_Point_refl. reflexivity.
      * destruct (eqb_Point x h) eqn:Heq; [simpl; rewrite Heq; reflexivity|].
        simpl. rewrite Heq. rewrite <- (reflect_iff _ _ IH). apply Hin'.
    + (* Reverse: linear_card_search x (h :: ls') = true -> In x (h :: ls'). *)
      intro Hmatch. destruct (x =? h) eqn:Heq.
      * rewrite <- (reflect_iff _ _ (eqb_Point_spec _ _)) in Heq.
        subst. apply in_eq.
      * unfold linear_card_search in Hmatch.
        rewrite Heq in Hmatch.
        fold linear_card_search in Hmatch.
        rewrite <- (reflect_iff _ _ IH) in Hmatch. apply in_cons. apply Hmatch.
Qed.

Theorem deck_complete : forall p : Point, In p entire_deck.
Proof.
  intros p.
  destruct p as [d1 d2 d3 d4].
  (* Case analysis on 81 cases. Somewhat ugly. *)
  destruct d1, d2, d3, d4;
  apply (reflect_iff _ _ (reflect_linear_card_search _ _)); reflexivity.
Qed.

