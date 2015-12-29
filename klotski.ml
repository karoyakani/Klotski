exception NotFound

type 'e rel = 'e -> 'e list
type 'e prop = 'e -> bool

type ('a, 'set) set_operations = {
  empty : 'set;              (* The empty set. *)
  mem : 'a -> 'set -> bool;  (* [mem x s = true] iff [x] is in [s]. *)
  add : 'a -> 'set -> 'set;  (* [add s x] is the set [s] union {x}. *)
}

type ('configuration, 'move) puzzle = {
  move : 'configuration -> 'move -> 'configuration;
  possible_moves : 'configuration -> 'move list;
  final : 'configuration -> bool
}

type piece_kind = S | H | V | C | X
type piece = piece_kind * int
let x = (X, 0) and s = (S, 0) and h = (H, 0)
let (c0, c1, c2, c3) = ((C, 0), (C, 1), (C, 2), (C, 3))
let (v0, v1, v2, v3) = ((V, 0), (V, 1), (V, 2), (V, 3))
let all_pieces : piece list = [ s; h; c0; c1; c2; c3; v0; v1; v2; v3 ]

type board = piece array array
let initial_board =
  [| [| v0 ; s  ; s  ; v1 |];
     [| v0 ; s  ; s  ; v1 |];
     [| v2 ; h  ; h  ; v3 |];
     [| v2 ; c0 ; c1 ; v3 |];
     [| c2 ; x  ; x  ; c3 |] |]

let initial_board_simpler =
  [| [| c2 ; s  ; s  ; c1 |] ;
     [| c0 ; s  ; s  ; c3 |] ;
     [| v1 ; v2 ; v3 ; v0 |] ;
     [| v1 ; v2 ; v3 ; v0 |] ;
     [| x  ; x  ; x  ; x  |] |]

let initial_board_trivial =
  [| [| x  ; s  ; s  ; x  |] ;
     [| x  ; s  ; s  ; x  |] ;
     [| x  ; x  ; x  ; x  |] ;
     [| x  ; x  ; x  ; x  |] ;
     [| x  ; x  ; x  ; x  |] |]

type direction = { dcol : int; drow : int; }
type move = Move of piece * direction * board
let move _ (Move (_, _, b)) = b

(* grade_only [ n ] *)

let rec loop p f x = match p x with
  | true -> x
  | false -> loop p f (f x) ;;

let rec exists p = function
  | [] -> false
  | x::xs -> if p x then true else exists p xs ;;

let rec find p = function
  | [] -> raise NotFound
  | x::xs -> if p x then x else find p xs ;;

(* --- Part A: A Generic Problem Solver --- *)

let near x = [x-2; x-1; x; x+1; x+2] ;;

let rec flat_map r l = List.concat (List.map r l) ;;

let rec iter_rel rel n = fun x ->
  match n with
  | 0 -> [x]
  | n -> flat_map rel (iter_rel rel (n-1) x) ;;

let solve r p x = 
  let rec aux l = if exists p l then find p l else aux (flat_map r l)
  in aux [x] ;;

let solve_path r p x =
  let r' = function [] -> [] | x::xs -> List.map (fun y -> y::x::xs) (r x) in
  let p' = function [] -> false | x::xs -> p x in
  let rec aux l = if exists p' l then find p' l else aux (flat_map r' l)
  in List.rev (aux [[x]]) ;;

let archive_map opset r (s, l) =
  let f (a,b) x = if opset.mem x a then (a,b) else (opset.add x a, x::b) in 
  List.fold_left f (s, []) (flat_map r l)

let solve' opset r p x =
  let rec aux (s, l) =
    if exists p l then find p l else aux (archive_map opset r (s, l))
  in aux (opset.empty, [x]) ;;

let solve_path' opset r p x =
  let r' = function [] -> [] | x::xs -> List.map (fun y -> y::x::xs) (r x) in
  let p' = function [] -> false | x::xs -> p x in
  let rec aux (s, l) =
    if exists p' l then find p' l else aux (archive_map opset r' (s, l))
  in List.rev (aux (opset.empty, [[x]])) ;;

let solve_puzzle p opset = 
  let r c = List.map (p.move c) (p.possible_moves c) in
  solve_path' opset r p.final ;;

(* --- Part B: A Solver for Klotski --- *)

let final board = 
  let ss = function
    | [| _; (S,0); (S,0); _ |] -> true
    | _ -> false
  in
  let n = Array.length board in
  ss board.(n-2) && ss board.(n-1) ;;

let move_piece board piece { drow; dcol } =
  let locate1 vec =
    let rec find1 j = if vec.(j) = piece then j else find1 (j+1)
    in find1 0
  in
  let rec find2 i =
    try
      let j = locate1 board.(i) in (i, j)
    with _ when i<Array.length board-1 -> find2 (i+1)
  in
  let movable (r, c) (ht, wd) =
    try
      match {drow; dcol} with
      | {drow = 1; dcol = 0} -> board.(r+ht +1).(c) = x && (wd = 0 || board.(r+ht +1).(c+wd) = x)
      | {drow = 0; dcol = 1} -> board.(r).(c+wd+1) = x && (ht  = 0 || board.(r+ht ).(c+wd+1) = x)
      | {drow = -1; dcol = 0} -> board.(r-1).(c) = x && (wd = 0 || board.(r-1).(c+wd) = x)
      | {drow = 0; dcol = -1} -> board.(r).(c-1) = x && (ht  = 0 || board.(r+ht ).(c-1) = x)
      | _ -> false
    with _ -> false
  in
  let move_it (r, c) (ht , wd) =
    let bd = Array.map Array.copy board in
    let swap (r0,c0) (r1,c1) =
      (bd.(r0).(c0) <- board.(r1).(c1); bd.(r1).(c1) <- board.(r0).(c0))
    in
    let mv =
      (match {drow; dcol} with
      | {drow = 1; dcol = 0} -> (swap (r,c) (r+ht +1,c); if wd = 1 then swap (r,c+wd) (r+ht +1,c+wd))
      | {drow = 0; dcol = 1} -> (swap (r,c) (r,c+wd+1); if ht  = 1 then swap (r+ht ,c) (r+ht ,c+wd+1))
      | {drow = -1; dcol = 0} -> (swap (r+ht ,c) (r-1,c); if wd = 1 then swap (r+ht ,c+wd) (r-1,c+wd))
      | {drow = 0; dcol = -1} -> (swap (r,c+wd) (r,c-1); if ht  = 1 then swap (r+ht ,c+wd) (r+ht ,c-1))
      | _ -> ())
    in
    (mv; Some bd)
  in
  try
    let (r, c) = find2 0 in
    match piece with
    | (S,0) when movable (r, c) (1,1) -> move_it (r, c) (1,1)
    | (H,0) when movable (r, c) (0,1) -> move_it (r, c) (0,1)
    | (C,0) when movable (r, c) (0,0) -> move_it (r, c) (0,0)
    | (C,1) when movable (r, c) (0,0) -> move_it (r, c) (0,0)
    | (C,2) when movable (r, c) (0,0) -> move_it (r, c) (0,0)
    | (C,3) when movable (r, c) (0,0) -> move_it (r, c) (0,0)
    | (V,0) when movable (r, c) (1,0) -> move_it (r, c) (1,0)
    | (V,1) when movable (r, c) (1,0) -> move_it (r, c) (1,0)
    | (V,2) when movable (r, c) (1,0) -> move_it (r, c) (1,0)
    | (V,3) when movable (r, c) (1,0) -> move_it (r, c) (1,0)
    | _ -> None
  with
    _ -> None ;;

let possible_moves board =
  let add_dirmv pc acc dir =
    match move_piece board pc dir with
    | Some bd -> Move (pc, dir, bd)::acc
    | _ -> acc
  in
  let dirs =
    [{drow = 1; dcol = 0}; {drow = 0; dcol = 1}; {drow = -1; dcol = 0}; {drow = 0; dcol = -1}]
  in
  let add_moves acc pc = List.fold_left (add_dirmv pc) acc dirs
  in
  List.fold_left add_moves [] all_pieces ;;

let klotski : (board, move) puzzle = { move; possible_moves; final }

module BoardSet =
  Set.Make (struct
    type t = board
    let compare b1 b2 =
      let cmpk k k' = if k = k' then 0 else
        match (k, k') with
        | S, _ -> 1
        | _, S -> -1
        | H, _ -> 1
        | _, H -> -1
        | C, _ -> 1
        | _, C -> -1
        | V, _ -> 1
        | _, V -> -1
        | _, _ -> 0
      in
      (* an exercise solution; however for better performance use the latter
      let cmpp (k,n) (k',n') = match cmpk k k' with 0 -> compare n n' | e -> e in
      *)
      let cmpp (k,n) (k',n') = match cmpk k k' in
      let rec cmp1 j b b' = 
        try match cmpp b.(j) b'.(j) with
          | 0 when j<3 -> cmp1 (j+1) b b'
          | e -> e
        with _ -> 0
      in
      let rec cmp2 i =
        try match cmp1 0 b1.(i) b2.(i) with
          | 0 when i<4 -> cmp2 (i+1)
          | e -> e
        with _ -> 0
      in
      cmp2 0
  end)

let solve_klotski =
  let opset = { 
    empty = BoardSet.empty; 
    mem = (fun l -> BoardSet.mem (List.hd l));
    add = (fun l -> BoardSet.add (List.hd l))}
  in
  solve_puzzle klotski opset

(* tests *)
let a1 = solve_klotski initial_board_trivial ;;
let a2 = solve_klotski initial_board_simpler ;;
let a3 = solve_klotski initial_board ;;

display_solution a1 ;;
display_solution a2 ;;
display_solution a3 ;;
