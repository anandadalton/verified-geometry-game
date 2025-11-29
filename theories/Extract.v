Require Import Affine.
Require Import GameState.
Require Import Extraction.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Set Extraction Output Directory ".".

Extraction "game_engine.ml"
  Point mkPoint F3 F0 F1 F2
  game_engine.
