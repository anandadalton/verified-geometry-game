From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
Open Scope Z_scope.

Record Rect := mkRect {
  x : Z;
  y : Z;
  w : Z;
  h : Z;
}.

Definition is_inside (px py : Z) (r : Rect) : bool :=
  (r.(x) <=? px) && (px <=? r.(x) + r.(w)) &&
  (r.(y) <=? py) && (py <=? r.(y) + r.(h)).


Definition card_w : Z := 80.
Definition card_h : Z := 120.
Definition gap_x : Z := 15.
Definition gap_y : Z := 15.
Definition start_x : Z := 20.
Definition start_y : Z := 20.

Definition get_rect_for_slot (col_idx row_idx : Z) : Rect :=
  let x_pos := start_x + (col_idx * (card_w + gap_x)) in
  let y_pos := start_y + (row_idx * (card_h + gap_y)) in
  mkRect x_pos y_pos card_w card_h.