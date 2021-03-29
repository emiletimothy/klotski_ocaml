(* search.ml: search strategies *)
(* Student name: Emile Timothy Anand *)
(* CMS cluster login name: eanand *)

module type Storage =
  sig
    type 'a t
    exception Empty

    val create : unit -> 'a t
    val push : 'a -> 'a t -> unit
    val pop : 'a t -> 'a
    val is_empty : 'a t -> bool
  end

module type Domain =
  sig
    type t
    val show : t -> string
    val is_solved : t -> bool
    val compare : t -> t -> int
    val next : t -> t list
  end

module Search (S : Storage) (D : Domain) =
  struct
    module DS = Set.Make(D)

  (*
  Create a new Storage structure (using S.create).
  Create a history which is just a list containing the initial board. Push it onto the storage structure.
  Create an empty set of visited boards (using DS.empty).
  Repeat the following steps:
  If the storage structure is empty, the search has failed, so raise the Not_found exception.
  Otherwise, pop a history off the storage structure. Then:
  Check the most recent board in the history. If it has already been seen (use the set of visited boards to check for this), throw the history away and go to the next one.
  Otherwise, check to see if the board solves the problem. If so, return the history and you’re done!
  Otherwise, add the board to the set of visited boards, find the children of the current board (using the D.next function, which will actually be the next function you wrote in part A), generate the new histories, and push them back onto the storage structure. Then continue.
  *)

  let rec find_history next history n v =
      match next with
      | [] -> n
      | h::t -> if DS.mem h v then find_history t history n v else find_history t history ([h::history] @ n) v

  let rec update_visited next v =
    match next with
    | [] -> v
    | h::t -> update_visited t (DS.add h v)
  
    let rec store_history history storage unit_p =
      match history with
      | [] -> storage
      | h::t -> store_history t storage (S.push h storage)

  let search init =
    let storage = S.create () in
    let rec searcher storage p v =
      match S.is_empty storage with
      | true -> raise Not_found
      | _ -> let e = S.pop storage in
        match D.is_solved (List.hd e) with
        | true -> e
        | _ -> let n = D.next (List.hd e) in 
        searcher(store_history (find_history n e [] v) storage ()) p (update_visited n v)
    in searcher storage (S.push [init] storage) (DS.add init (DS.empty))

    let show_history hist =
      (String.concat "\n----\n\n" (List.map D.show (List.rev hist))) ^ "\n"
  end

