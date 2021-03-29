(* klotski.ml: core functionality of the Klotski game. *)
(* Student name: Emile Timothy Anand *)
(* CMS cluster login name: eanand *)

(* ---------------------------------------------------------------------- 
 * Types.
 * ---------------------------------------------------------------------- *)

type loc = int * int
type dir = Up | Down | Left | Right
type move = char * dir * int

module LocM =
  struct
    type t = loc
    let compare = Stdlib.compare
  end

module LocSet : Set.S with type elt = loc = Set.Make(LocM)

(* Sets of LocSets.  Used locally only. *)

module LocSetM =
  struct
    type t = LocSet.t
    let compare = LocSet.compare
  end

module LocSetSet = Set.Make(LocSetM)

module CharM =
  struct
    type t = char
    let compare = Stdlib.compare
  end

module CharMap : Map.S with type key = char = Map.Make(CharM)

type piece = LocSet.t
type t = { pieces : piece CharMap.t ; unoccupied : LocSet.t }

(* ---------------------------------------------------------------------- 
 * Functions.
 * ---------------------------------------------------------------------- *)

(* Create a board from a string. *)
let read s = 
  let rec iter p u r c =
    match () with
      | _ when r = 5 -> { pieces = p; unoccupied = u }
      | _ when c = 4 -> iter p u (r + 1) 0 
      | _ -> 
        let i = r * 4 + c in
        let ch = s.[i] in
          if ch = '.'  (* unoccupied location; add to unoccupied set *)
            then iter p (LocSet.add (r, c) u) r (c + 1)
            else  (* occupied; add to appropriate piece set *)
              try
                let cs  = CharMap.find ch p in     (* old piece set *)
                let cs' = LocSet.add (r, c) cs in  (* add new location *)
                let p'  = CharMap.add ch cs' p in  (* store back into map *)
                  iter p' u r (c + 1)
              with
                Not_found ->  (* new piece; create a new piece set *)
                  let cs = LocSet.singleton (r, c) in
                  let p' = CharMap.add ch cs p in
                    iter p' u r (c + 1)
  in
    if String.length s <> 20
      then failwith "read: invalid input string length"
      else iter CharMap.empty LocSet.empty 0 0

(* Convert the board to a string representation suitable for printing. *)
let show b = 
  let string_of_char_list = function
    | [a;b;c;d] -> Printf.sprintf "%c%c%c%c" a b c d
    | _ -> failwith "invalid char list"
  in
  let char_at board loc =
    let rec iter = function
      | [] -> raise Not_found
      | (c, locs) :: t -> 
        if LocSet.mem loc locs then c else iter t
    in
    if LocSet.mem loc board.unoccupied
      then '.'
      else iter (CharMap.bindings board.pieces)
  in
  (String.concat "\n"
     (List.map (fun r ->
        string_of_char_list
          (List.map (char_at b) 
            (List.map (fun c -> (r, c)) [0; 1; 2; 3])))
        [0; 1; 2; 3; 4])) ^ "\n"
;;

let is_solved b = 
  CharMap.exists (fun p m -> LocSet.equal (LocSet.of_list [(3, 1); (4, 1); (3, 2); (4, 2)]) m) (b.pieces)
;;

let help_compare b = 
  let rec location_set b full = 
    match b with
    | [] -> full
    | (_, a) :: t -> location_set t (LocSetSet.add a full)
  in location_set b LocSetSet.empty
;;

let compare b1 b2 = let cmp = LocSet.compare b1.unoccupied b2.unoccupied in
  if cmp <> 0 then
    cmp
  else
    LocSetSet.compare (help_compare (CharMap.bindings b1.pieces)) (help_compare (CharMap.bindings b2.pieces))
;;

let remove c ({ pieces = p; unoccupied = u } as b) =
  if CharMap.mem c p then
    {pieces = CharMap.remove c b.pieces; unoccupied = LocSet.union (CharMap.find c b.pieces) b.unoccupied}
  else
    b
;;

let intersection x y = 
  let rec set_diff x y = 
    match x with
      | [] -> y
      | h::t -> set_diff t (LocSet.remove h y)
  in set_diff x y
;;

let add (c, p) { pieces = ps; unoccupied = u } = 
  if (CharMap.mem c ps == false) && (LocSet.subset p u) then
    Some {pieces = CharMap.add c p ps; unoccupied = (intersection (LocSet.elements p) u)}
  else 
    None
;;

let helper_move label direction board = 
  let b1 = CharMap.find label board.pieces in
  let b2 = remove label board in
  let matched = match direction with
    | Left -> fun (y, x) -> (y, x - 1)
    | Right -> fun (y, x) -> (y, x + 1)
    | Up -> fun (y, x) -> (y - 1, x)
    | Down -> fun (y, x) -> (y + 1, x)
  in
  add (label, LocSet.map matched b1) b2
;;

let make_move (c, d, i) b =
  if (CharMap.mem c b.pieces && i >= 1) then 
    let rec one_move (c1, d1, i1) b1 = 
      match i1 with
        | 0 -> Some b1 (* stop recursing - it's a valid move *)
        | _ -> match helper_move c1 d1 b1 with
          | None -> None (* stop recursing - move isn't valid *)
          | Some b1 -> one_move (c1, d1, i1 - 1) b1
    in one_move (c, d, i) b
  else
    None
;;

let moves_for_piece_in_one_dir label dir to_i board = 
  let rec find lab dir to_i lst board = 
    if to_i = 0 then lst else
      match make_move (lab, dir, to_i) board with
        | None -> find lab dir (to_i - 1) lst board
        | Some move -> find lab dir (to_i - 1) (move :: lst) board
  in find label dir to_i [] board
;;

let all_moves_for_one_piece label board = 
  moves_for_piece_in_one_dir label Up 4 board @
  moves_for_piece_in_one_dir label Down 4 board @
  moves_for_piece_in_one_dir label Left 4 board @
  moves_for_piece_in_one_dir label Right 4 board
;;

let charmap_key_lst board = 
  let rec get_key_lst lst board = match board with
      | (lab, _)::t -> get_key_lst (lab::lst) t
      | [] -> lst
  in get_key_lst [] (CharMap.bindings board.pieces)
;;

let next b = 
  let rec get_next lst label b = 
    match label with
      | h::t -> get_next (all_moves_for_one_piece h b @ lst) t b
      | [] -> lst
  in get_next [] (charmap_key_lst b) b;;
;;


(* Function to interactively test the "next" function. 
 * Useful for debugging. *)
let test_next b =
  let bs = next b in
    begin
      print_string (show b ^ "\n");
      List.iter 
        (fun b -> print_string ("----\n\n" ^ show b ^ "\n"))
        bs
    end
;;

