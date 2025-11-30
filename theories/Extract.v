Require Import Affine.
Require Import Deck.
Require Import GameState.
Require Import Display.
Require Import Extraction.
Require Import ClientState.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Set Extraction Output Directory ".".

Extraction "game_engine.ml"
  Point mkPoint F3 F0 F1 F2
  entire_deck
  selection_contains
  CardTriple mkTriple 
  State mkState
  game_engine
  sync_grid
  Model mkModel
  init_model
  Status MsgSelect MsgChecking MsgMatch MsgInvalid MsgGameOver
  ui_update.
