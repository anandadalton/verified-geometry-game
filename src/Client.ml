open Game_engine
open Brr
open Brr_canvas

let () = Random.self_init ()

let shuffle list =
  let arr = Array.of_list list in
  let n = Array.length arr in
  for i = n - 1 downto 1 do
    let j = Random.int (i + 1) in
    let temp = arr.(i) in
    arr.(i) <- arr.(j);
    arr.(j) <- temp
  done;
  Array.to_list arr

let f3_to_int = function
  | Game_engine.F0 -> 0
  | Game_engine.F1 -> 1
  | Game_engine.F2 -> 2

let get_color_str val_f3 =
  match val_f3 with
  | Game_engine.F0 -> "rgb(255, 50, 50)" (* Red *)
  | Game_engine.F1 -> "rgb(50, 200, 50)" (* Green *)
  | Game_engine.F2 -> "rgb(150, 50, 255)" (* Purple *)

module C2d = Brr_canvas.C2d
module Path = Brr_canvas.C2d.Path

let status_to_string = function
  | MsgSelect -> "Select 3 cards..."
  | MsgMatch -> "Match Found!"
  | MsgInvalid -> "Not a Valid Match"
  | MsgGameOver -> "Game Over! Refresh to Restart"

let define_shape path shape_type size =
  let r = size /. 2.0 in
  match shape_type with
  | Game_engine.F0 ->
     Path.arc path ~cx:0. ~cy:0. ~r ~start:0. ~stop:(2. *. Float.pi)
  | Game_engine.F1 ->
     Path.rect path ~x:(-.r) ~y:(-.r) ~w:size ~h:size
  | Game_engine.F2 ->
     Path.move_to path ~x:0. ~y:(-.r);
     Path.line_to path ~x:r ~y:r;
     Path.line_to path ~x:(-.r) ~y:r;
     Path.close path
 
type card_style =
  | Normal
  | Selected
  | Success
  | Failure
  | NewArrival

let draw_card ctx card x y w h style =
  C2d.save ctx;
  C2d.translate ctx ~x ~y;

  let border_color = match style with
    | Normal -> Jstr.v "#333"
    | Selected -> Jstr.v "gold"
    | Success -> Jstr.v "#32CD32"
    | Failure -> Jstr.v "red"
    | NewArrival -> Jstr.v "#1E90FF"
  in

  let line_width = match style with Normal -> 2.0 | _ -> 6.0 in

  C2d.set_stroke_style ctx (C2d.color border_color);
  C2d.set_line_width ctx line_width;
  C2d.set_fill_style ctx (C2d.color (Jstr.v "white"));

  C2d.fill_rect ctx ~x:0. ~y:0. ~w ~h;

  let stroke_offset = if style = Normal then 0. else (-3.) in
  let stroke_size = if style = Normal then 0. else 6. in
  C2d.stroke_rect ctx ~x:stroke_offset ~y:stroke_offset ~w:(w+.stroke_size) ~h:(h+.stroke_size);

  let dim1 = card.d1 in
  let dim2 = card.d2 in
  let dim3 = card.d3 in
  let dim4 = card.d4 in

  let color = Jstr.v (get_color_str dim2) in
  C2d.set_stroke_style ctx (C2d.color color);
  C2d.set_line_width ctx 3.0;

  let count = (f3_to_int dim3) + 1 in
  let center_x = w /. 2.0 in
  let center_y = h /. 2.0 in
  
  let shape_size = w /. 3.2 in

  let positions = match count with
  | 1 ->
    [ (0., 0.) ]
  | 2 ->
    let offset = h /. 4.5 in
    [ (0., -.offset); (0., offset) ]
  | 3 ->
    let top_y = -.(h /. 4.5) in
    let bot_y = (h /. 5.0) in
    let x_off = (w /. 4.0) in
    [
      (0., top_y);
      (-.x_off, bot_y);
      (x_off, bot_y)
    ]
  | _ -> []
  in

  List.iter (fun (dx, dy) ->
    C2d.save ctx;
    C2d.translate ctx ~x:(center_x +. dx) ~y:(center_y +. dy);

    let p = Path.create () in
    define_shape p dim1 shape_size;

    begin match dim4 with
    | Game_engine.F0 ->
      C2d.set_fill_style ctx (C2d.color color);
      C2d.fill ctx p
    | Game_engine.F1 ->
      ()
    | Game_engine.F2 ->
      C2d.set_fill_style ctx (C2d.color color);
      C2d.set_global_alpha ctx 0.3;
      C2d.fill ctx p;
      C2d.set_global_alpha ctx 1.0;
    end;
    
    C2d.stroke ctx p;
    C2d.restore ctx;
  ) positions;
  C2d.restore ctx

let render_scene ctx state =
  C2d.clear_rect ctx ~x:0. ~y:0. ~w:1000. ~h:1000.;

  let core = state.Game_engine.game_state in

  let phase = core.current_phase in

  let get_style card =
    match phase with
    | AnimatingMatch (MkTriple (c1, c2, c3)) ->
      if card = c1 || card = c2 || card = c3 then Success else Normal
    | AnimatingFail (MkTriple (c1, c2, c3)) ->
      if card = c1 || card = c2 || card = c3 then Failure else Normal
    | AnimatingDeal new_cards ->
      if List.exists (fun c -> c = card) new_cards then NewArrival else Normal
    | UserSelecting selected_list ->
      if selection_contains card selected_list then Selected else Normal
    | GameOver -> Normal
    in

  let renderables = Game_engine.layout_grid state.display_grid in
  List.iter (fun (card, rect) ->
    let x = float_of_int rect.Game_engine.x in
    let y = float_of_int rect.Game_engine.y in
    let w = float_of_int rect.Game_engine.w in
    let h = float_of_int rect.Game_engine.h in

    let style = get_style card in
    draw_card ctx card x y w h style
  ) renderables;

  C2d.set_fill_style ctx (C2d.color (Jstr.v "black"));
  C2d.set_font ctx (Jstr.v "24px sans-serif");
  let msg = status_to_string state.status_message in
  C2d.fill_text ctx (Jstr.v msg) ~x:20. ~y:450.

let app_state = ref None

let rec perform_update ctx evt =
  match !app_state with
  | None -> ()
  | Some current_model ->
    let new_model = Game_engine.ui_update evt current_model in
    app_state := Some new_model;
    render_scene ctx new_model;
    handle_side_effects ctx current_model.game_state.current_phase new_model.game_state.current_phase

and handle_side_effects ctx old_phase new_phase =
  if old_phase <> new_phase then
    match new_phase with
    | AnimatingMatch _ ->
      ignore (Brr.G.set_timeout ~ms:1000 (fun () -> perform_update ctx TimerDone))
    | AnimatingFail _ ->
      ignore (Brr.G.set_timeout ~ms:600 (fun () -> perform_update ctx TimerDone))
    | AnimatingDeal _ ->
      ignore (Brr.G.set_timeout ~ms:400 (fun () -> perform_update ctx TimerDone))
    | _ -> ()
 
let on_click ctx x y =
  match !app_state with
  | None -> ()
  | Some model ->
    match model.game_state.current_phase with
    | UserSelecting _ ->
      let ix = int_of_float x in
      let iy = int_of_float y in
      perform_update ctx (Game_engine.ClickAt (ix, iy))

    | _ -> () (* Ignore clicks during animations *)


let () =
  let entry () =
    match Document.find_el_by_id G.document (Jstr.v "board") with
    | None -> Console.(error [str "No canvas found!"])
    | Some el ->
        let canvas = Canvas.of_el el in
        let ctx = C2d.get_context canvas in
        let full_deck_points = Game_engine.entire_deck in
        let shuffled = shuffle full_deck_points in
        let initial_model = Game_engine.init_model shuffled in
        app_state := Some initial_model;
        render_scene ctx initial_model;
        let on_mouse_event ev_wrapper =
          let ev = Ev.as_type ev_wrapper in
          let x = Ev.Mouse.offset_x ev in
          let y = Ev.Mouse.offset_y ev in
          on_click ctx x y
        in
        ignore (Ev.listen Ev.click on_mouse_event (El.as_target el))
  in
  entry ()
