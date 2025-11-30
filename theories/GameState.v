Require Import Eqb Affine Referee Deck.
From Stdlib Require Import Arith Bool List.
Import ListNotations.


(* Since we have so many cases where we deal with either exactly three or
   strictly less than three cards, it makes sense to have custom datatypes
   (make illegal states impossible to represent). *)

Inductive Selection :=
| Sel0
| Sel1 (c1 : Point)
| Sel2 (c1 c2 : Point).

Inductive CardTriple := mkTriple (c1 c2 c3 : Point).

Inductive SelectResult :=
| NewSel (s : Selection)
| TriggerCheck (t : CardTriple).

Definition selection_contains (p : Point) (s : Selection) : bool :=
  match s with
  | Sel0 => false
  | Sel1 c1 => (c1 =? p)
  | Sel2 c1 c2 => (c1 =? p) || (c2 =? p)
  end.

(* This is mildly annoying compared to fixpoints over lists.
   As this evolves I should check whether I'm happy with this choice. *)
Definition handle_click (current : Selection) (p : Point) : SelectResult :=
  match current with
  | Sel0 => NewSel (Sel1 p)
  | Sel1 c1 =>
    if c1 =? p then NewSel Sel0 else NewSel (Sel2 c1 p)
  | Sel2 c1 c2 =>
    if c1 =? p then NewSel (Sel1 c2)
    else if c2 =? p then NewSel (Sel1 c1)
    else TriggerCheck (mkTriple c1 c2 p)
  end.

Inductive Event :=
| CardClick (card : Point)
| AnimationDone.

Inductive Phase :=
| UserSelecting (selection : Selection)
| AnimatingMatch (triple : CardTriple)
| AnimatingFail (triple : CardTriple)
  (* Note that we may end up dealing more than three cards at once. *)
| AnimatingDeal (new_cards : list Point)
| GameOver.

Record State : Type := mkState {
  (* We use CardTriple because we always deal in groups of three cards. *)
  deck : list CardTriple;
  board : list Point;
  current_phase : Phase;
}.

Fixpoint remove_point (p : Point) (ls : list Point) : list Point :=
  match ls with
  | [] => []
  | (h :: ls') => if (h =? p) then ls' else h :: (remove_point p ls')
  end.

Definition remove_triple (t : CardTriple) (ls : list Point) : list Point :=
  match t with
  | mkTriple c1 c2 c3 => remove_point c3 (remove_point c2 (remove_point c1 ls))
  end.

Definition should_stop (board : list Point) :=
  referee board && Nat.leb 12 (length board).

(* The third parameter is to track cards that have been dealt;
   this is primarily a convenience for animating them. *)
Fixpoint deal (deck : list CardTriple) (board : list Point) (dealt : list Point)
    : (list CardTriple * list Point * list Point) :=
  if should_stop board then
    (deck, board, dealt)
  else
    match deck with
    | [] => ([], board, dealt)
    | ((mkTriple c1 c2 c3) :: deck') =>
      let board' := c1 :: c2 :: c3 :: board in
      let dealt' := c1 :: c2 :: c3 :: dealt in
        deal deck' board' dealt'
    end.

Definition after_deal_invariant (deck_board : list CardTriple * list Point) :=
  fst deck_board = [] \/ ((has_valid_triple (snd deck_board) /\ 12 <= length (snd deck_board))).

Lemma stopping_condition_sound : forall (remaining_deck : list CardTriple) (board : list Point),
  should_stop board = true -> after_deal_invariant (remaining_deck, board).
Proof.
  intros deck board Hstop.
  unfold after_deal_invariant, should_stop in *.
  right.
  apply andb_prop in Hstop. destruct Hstop as [Hmatch Hlen].
  split.
  - apply (reflect_iff _ _ (reflect_has_valid_triple_referee _)); assumption.
  - apply Nat.leb_le; assumption.
Qed.

(* This is very trivial in the current formulation of deal but it is
   important if we ever refactor it. In particular, an early implementation
   always dealt three even if should_stop was true. *)
Theorem deal_can_do_nothing :
  forall (deck : list CardTriple) (board : list Point) (dealt : list Point), 
  should_stop board = true ->
  deal deck board dealt = (deck, board, dealt).
Proof.
  intros deck board dealt Hstop.
  (* I think for some reason the structure of the Fixpoint makes us need to
     induct or at least destruct. Irritating! *)
  destruct deck as [|h deck']; unfold deal; rewrite Hstop; reflexivity.
Qed.

Theorem deal_satisfies_invariant :
  forall (deck : list CardTriple) (board : list Point) (dealt : list Point),
  after_deal_invariant (fst (deal deck board dealt)).
Proof.
  intros deck.
  induction deck as [|h deck' IH]; intros board dealt.
  - simpl. left. destruct (should_stop board); reflexivity.
  - destruct h as [c1 c2 c3]. simpl.
    destruct (should_stop board) eqn:Hstop.
    + apply stopping_condition_sound. assumption.
    + apply IH.
Qed.

(* I think it might also be smart to add some sort of a Reset button so that users
   can begin a new game when the game is over (or in case they give up).

   Note to self: there is some neat syntactic sugar apparently for "updating"
   fields, but I don't know if I want to add coq-record-update to this toy
   just for that reason. *)
Definition game_engine (s : State) (e : Event) : State :=
  match s.(current_phase), e with
  | UserSelecting selection, CardClick card =>
    match handle_click selection card with
    | NewSel new_selection => {| deck := s.(deck); board := s.(board); current_phase := UserSelecting new_selection |}
    | TriggerCheck (mkTriple c1 c2 c3 as t) =>
      if algebraic_validb_points c1 c2 c3
      then {| deck := s.(deck); board := s.(board); current_phase := AnimatingMatch t |}
      else {| deck := s.(deck); board := s.(board); current_phase := AnimatingFail t |}
    end
  | UserSelecting _, AnimationDone => s (* AnimationDone should not happen. *)
  | AnimatingMatch _, CardClick _ => s (* Ignore user input during animations. *)
  | AnimatingMatch selection, AnimationDone =>
    let board_minus_match := remove_triple selection s.(board) in
      let '(deck', board', dealt) := deal s.(deck) board_minus_match [] in
        match dealt with
        | [] => if referee board'
                then {| deck := deck'; board := board'; current_phase := UserSelecting Sel0 |}
                else {| deck := deck'; board := board'; current_phase := GameOver |}
        | _ => {| deck := deck'; board := board'; current_phase := AnimatingDeal dealt |}
        end
  | AnimatingFail _, CardClick _ => s (* Ignore user input during animations. *)
  | AnimatingFail selection, AnimationDone =>
      {| deck := s.(deck); board := s.(board); current_phase := UserSelecting Sel0 |}
  | AnimatingDeal _, CardClick _ => s (* Ignore user input during animations. *)
  | AnimatingDeal selection, AnimationDone =>
      if referee s.(board)
      then {| deck := s.(deck); board := s.(board); current_phase := UserSelecting Sel0 |}
      else {| deck := s.(deck); board := s.(board); current_phase := GameOver |}
  | GameOver, _ => s
  end.

Fixpoint group_into_triples (l : list Point) : list CardTriple :=
  match l with
  | c1 :: c2 :: c3 :: tail => (mkTriple c1 c2 c3) :: (group_into_triples tail)
  | _ => []
  end.

Definition init_state (shuffled_raw : list Point) : State :=
  let safe_deck := group_into_triples shuffled_raw in
  let '(start_deck, start_board, _) := deal safe_deck [] [] in
  {|
    deck := start_deck;
    board := start_board;
    current_phase := UserSelecting Sel0;
  |}.
