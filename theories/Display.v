From Stdlib Require Import Bool List ZArith.
Import ListNotations.

Require Import Affine.
Require Import Geometry.

Definition Slot := option Point.
Record Column : Type := mkColumn {
r1 : Slot;
r2 : Slot;
r3 : Slot;
}.

Definition Grid := list Column.

Definition empty_col : Column := mkColumn None None None.

(* Drop any cards that are not represented in the hand. *)
Definition gc_slot (s : Slot) (hand : list Point) : Slot :=
  match s with
  | None => None
  | Some p => if existsb (fun h => eqb_Point h p) hand then Some p else None
  end.

Definition gc_grid (g : Grid) (hand : list Point) : Grid :=
  map (fun c =>
    mkColumn
      (gc_slot (r1 c) hand)
      (gc_slot (r2 c) hand)
      (gc_slot (r3 c) hand)
  ) g.

(* Returns: (Updated Column, Remaining Cards) *)
Definition fill_column (c : Column) (cards : list Point) : (Column * list Point) :=
  let '(val_r1, cards_after_r1) :=
    match r1 c, cards with
    | None, p :: cards' => (Some p, cards')
    | current, _ => (current, cards)
    end
  in
  let '(val_r2, cards_after_r2) :=
    match r2 c, cards_after_r1 with
    | None, p :: cards' => (Some p, cards')
    | current, _ => (current, cards_after_r1)
    end
  in
  let '(val_r3, cards_after_r3) :=
    match r3 c, cards_after_r2 with
    | None, p :: cards' => (Some p, cards')
    | current, _ => (current, cards_after_r2)
    end
  in (mkColumn val_r1 val_r2 val_r3, cards_after_r3).

(* Returns: (Updated Grid, Cards that didn't fit) *)
Fixpoint fill_existing (g : Grid) (cards : list Point) : (Grid * list Point) :=
  match g with
  | [] => ([], cards)
  | col :: rest_g =>
    let '(filled_col, remaining_cards) := fill_column col cards in
    let '(filled_rest, final_cards) := fill_existing rest_g remaining_cards in
      (filled_col :: filled_rest, final_cards)
  end.

(* If we didn't have room for all the cards in the grid, populate them into additional columns. *)
Fixpoint create_columns (cards : list Point) : Grid :=
  match cards with
  | [] => []
  | c1 :: c2 :: c3 :: rest => (mkColumn (Some c1) (Some c2) (Some c3)) :: (create_columns rest)
  | _ =>
    let '(last_col, _) := fill_column empty_col cards in
    [last_col]
  end.

Definition fill_grid (g : Grid) (cards : list Point) : Grid :=
  let '(filled_g, leftovers) := fill_existing g cards in
  filled_g ++ (create_columns leftovers).

Definition flatten_grid (g : Grid) : list Point :=
  flat_map (fun c =>
    let l1 := match r1 c with Some p => [p] | None => [] end in
    let l2 := match r2 c with Some p => [p] | None => [] end in
    let l3 := match r3 c with Some p => [p] | None => [] end in
    l1 ++ l2 ++ l3
  ) g.

Definition is_empty_col (c : Column) : bool :=
  match r1 c, r2 c, r3 c with
  | None, None, None => true
  | _, _, _ => false
  end.

Fixpoint prune_grid (g : Grid) : Grid :=
  match g with
  | [] => []
  | c :: g' =>
    let pruned_g' := prune_grid g' in
    match pruned_g' with
    | [] =>
      (* We are at the end of the board. Is this column empty? *)
      if is_empty_col c then [] else [c]
    | _ =>
      c :: pruned_g'
    end
  end.

Definition sync_grid (old_grid : Grid) (flat_board : list Point) : Grid :=
  let clean_grid := gc_grid old_grid flat_board in
  let flattened_grid := flatten_grid clean_grid in
  let to_add := filter (fun p => negb (existsb (fun v => eqb_Point v p) flattened_grid)) flat_board in
  let filled_grid := fill_grid clean_grid to_add in
  prune_grid filled_grid.

Definition layout_grid (g : Grid) : list (Point * Rect) :=
  (fix loop_cols (cols : Grid) (col_idx : Z) : list (Point * Rect) :=
    match cols with
    | [] => []
    | c :: rest =>
      let col_items :=
        match r1 c with Some p => [(p, get_rect_for_slot col_idx 0)] | None => [] end ++
        match r2 c with Some p => [(p, get_rect_for_slot col_idx 1)] | None => [] end ++
        match r3 c with Some p => [(p, get_rect_for_slot col_idx 2)] | None => [] end
      in
      col_items ++ (loop_cols rest (col_idx + 1))
    end
  ) g 0.

Definition resolve_click (g : Grid) (x y : Z) : option Point :=
  let items := layout_grid g in
  let hit := find (fun item =>
    let '(_, r) := item in is_inside x y r
  ) items in
  match hit with
  | Some (p, _) => Some p
  | None => None
  end.

