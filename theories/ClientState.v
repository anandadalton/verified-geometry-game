Require Import Affine GameState Display.
From Stdlib Require Import Bool List.
Import ListNotations.

Inductive Status : Type :=
  | MsgSelect | MsgMatch | MsgInvalid | MsgGameOver.

Record Model : Type := mkModel {
  game_state : State;
  display_grid : Grid;
  status_message : Status;
  game_over : bool;
}.

Definition init_model (shuffled_deck : list Point) : Model :=
  let game_state := init_state shuffled_deck in
  let empty_grid := [] in
  let initial_grid := sync_grid empty_grid game_state.(board) in
  
   mkModel game_state initial_grid MsgSelect false.

Definition ui_update (event : Event) (m : Model) : Model :=
  let new_game_state := game_engine m.(game_state) event in
  let new_grid := sync_grid (display_grid m) new_game_state.(board) in
  let new_status := match current_phase new_game_state with
  | UserSelecting _ => MsgSelect
  | AnimatingMatch _ => MsgMatch
  | AnimatingFail _ => MsgInvalid
  | AnimatingDeal _ => MsgSelect
  | GameOver => MsgGameOver
  end in
  let is_over := match current_phase new_game_state with GameOver => true | _ => false end in
  mkModel new_game_state new_grid new_status is_over.

