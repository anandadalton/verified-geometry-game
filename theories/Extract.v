Require Import Affine.
Require Import Deck.
Require Import GameState.
Require Import Display.
Require Import Extraction.
Require Import ClientState.
Require Import Geometry.

From Stdlib Require Import ZArith.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extract Inductive positive => "int"
  [ "(fun x -> 2 * x + 1)" "(fun x -> 2 * x)" "1" ]
  "(fun f2p1 f2p f1 p ->
    if p <= 1 then f1 ()
    else if p mod 2 = 0 then f2p (p / 2)
    else f2p1 (p / 2))".

Extract Inductive N => "int"
  [ "0" "" ] 
  "(fun f0 fp n -> if n=0 then f0 () else fp n)".

Extract Inductive Z => "int"
 ["0" "(fun x -> x)" "(~-)" ]
 "(fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))".

Set Extraction Output Directory ".".

Extraction "game_engine.ml"
  Point mkPoint F3 F0 F1 F2
  entire_deck
  selection_contains
  CardTriple mkTriple
  Rect mkRect
  layout_grid
  State mkState
  game_engine
  sync_grid
  Model mkModel
  init_model
  Status MsgSelect MsgMatch MsgInvalid MsgGameOver
  ui_update.
