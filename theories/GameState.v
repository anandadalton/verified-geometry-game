Require Import Referee Deck Affine.
From Stdlib Require Import List.
Import ListNotations.

Inductive Phase :=
| UserSelecting (selection : list Point)
| AnimatingMatch (selection : list Point)
| AnimatingFail (selection : list Point)
| AnimatingDeal (new_cards : list Point)
| GameOver.

Record State : Type := mkState {
  deck : list Point;
  board : list Point;
  phase : Phase;
}.

(* State transitions, and how they occur:
- The game always starts in UserSelecting [], a board with 12 cards, and a deck
  with 81-12=69 cards.
- UserSelecting:
  + if an already-selected card is clicked, we remove it from selection.
  + if we click a new card, and we now have three cards, we check if it is a
    valid triple.
    * if it is a valid triple, we move to AnimatingMatch (with same selection).
    * if it is invalid, we move to AnimatingFail (with same selection).
    * if we don't have three cards after clicking a new card, we just add to
      the selection.
- AnimatingMatch: we do not transition out until we receive indication from the
  OCaml framework that the animation is done. Then we remove the three cards
  that were selected from the board, and we handle the logic for adding cards.
  + if there are no more cards in the deck, we don't add any new cards
    * if there are no more triples on the board, we transition to GameOver.
    * if there are still triples on the board, we transition to UserSelecting.
  + if there are still cards in the deck, and there are fewer than 12 cards on
    the board, we pop three cards from the deck and go to AnimatingDeal with
    those three cards.
  + if there are still cards in the deck, and there are more than 12 cards on
    the board:
    * if there is a triple on the board, we go directly to UserSelecting [].
    * if there is no triple on the board, we pop three cards from the deck and go
      to AnimatingDeal with those three cards.
- AnimatingFail: we do not transition until we receive indication from the
  OCaml framework that the animation is done. Then we go to UserSelecting [].
- AnimatingDeal: we do not transition until we receive indication from the
  OCaml framework that the animation is done. Then we add those three cards to
  the board, and we go directly to UserSelecting [].
- GameOver has no transitions away.

I think it might also be smart to add some sort of a Reset button so that users
can begin a new game when the game is over (or in case they give up). *)