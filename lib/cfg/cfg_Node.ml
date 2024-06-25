(* Internal static counter for generating incremental IDs *)
open Sexplib.Std
let counter = ref 0

let next_id () =
  counter := !counter + 1;
  !counter

module Node = struct
  (* Recursive definition of CFG node, made by
  *  id,
  *  exp,
  *  successors,
  *  predecessors
  *)
  type 'a t = {
      id            : int;
      mutable exp   : 'a;
      mutable succ  : 'a t list;
      mutable pred  : int list;
    } [@@deriving show, sexp]

  let compare (node1: 'a t) (node2: 'a t) : bool =
    (* Associate between the ids of the first node and the ids of the second node *)
    let associations = ref (Hashtbl.create 100) in
    (* lets hope that 100 is big enough *)
    Hashtbl.add !associations node1.id node2.id;

    let alreadyvisited = ref [] in

    let rec helper (node1: 'a t) (node2: 'a t) : bool =
      if List.mem node1.id !alreadyvisited then
        true
      else (
        alreadyvisited := node1.id :: !alreadyvisited;
        match (Hashtbl.find_opt !associations node1.id, node2.id) with
        | (Some a, b) -> (
          match (a == b, node1.exp = node2.exp, node1.succ, node2.succ) with
          | (true, true, [], []) -> true (* end of the graph *)
          | (true, true, [node1succ], [node2succ]) ->
             (* easy case, only 1 child *)
             Hashtbl.add !associations node1succ.id node2succ.id;
             helper node1succ node2succ
          | (true, true, a, b) when (List.length a) != (List.length b) ->
             (* not the right ammount of children *)
             false
          | (true, true, [n11; n12], [n21; n22]) -> (
            match (n11.exp = n21.exp, n11.exp = n22.exp) with
            | (true, _) -> (
              Hashtbl.add !associations n11.id n21.id;
              Hashtbl.add !associations n12.id n22.id;
              (helper n11 n21) && (helper n12 n22)
            )
            | (_, true) -> (
              Hashtbl.add !associations n11.id n22.id;
              Hashtbl.add !associations n12.id n21.id;
              (helper n11 n22) && (helper n12 n21)
            )
            | (false, false) -> false
          )
          | (true, true, _, _) -> (* Sir, This Is A Wendy's *)
             (* TODO: make it better and actually return true isomorphism
                (it's probably impossible to do in O(poly(n))) *)
             false
          | _ ->
             (* None so we've never seen this node before, should never happen *)
             false
        )
        | (None, _) ->
           (* first time we see node1 (happens only at the beginning) *)
           false
      )
    in
    helper node1 node2

  let length (node : 'a t) : int =
    let alreadyvisited = ref [] in
    let rec helper_length (node : 'a t) : int =
      if List.mem node.id !alreadyvisited then
        0
      else (
        alreadyvisited := node.id :: !alreadyvisited;
        match node.succ with
        | [] -> 1
        | [x] -> (helper_length x)+1
        | ls -> (
          List.map (fun x -> helper_length x) ls |>
            List.fold_left (+) 1
        )
      )
    in
    helper_length node

  let make (exp: 'a) (succ: 'a t list) (pred: int list) : 'a t =
    {id = next_id(); exp = exp; succ = succ; pred = pred}

  let make_with_id (id: int) (exp: 'a) (succ: 'a t list) (pred: int list) : 'a t =
    {id = id; exp = exp; succ = succ; pred = pred}

  let get_id (node: 'a t): int = node.id
  let get_exp (node : 'a t) : 'a = node.exp
  let get_succ (node : 'a t) : 'a t list = node.succ
  let get_pred (node : 'a t) : int list = node.pred

  let add_succ (node : 'a t) (succ : 'a t) : unit =
    node.succ <- succ    :: node.succ;
    succ.pred <- node.id :: succ.pred

  let add_pred (node : 'a t) (pred : int) : unit =
    node.pred <- pred::(node.pred)

  let set_exp (node : 'a t) (newexp : 'a) : unit =
    node.exp <- newexp

  let set_succ (node : 'a t) (succ : 'a t list) : unit =
    List.iter (fun x -> (* remove all backwards links*)
        x.pred <- List.filter (fun x -> x != node.id) x.pred
      ) node.succ;
    List.iter (fun x -> (* add new backwards links *)
        x.pred <- node.id :: x.pred
      ) succ;
    node.succ <- succ

  let remove_pred (node : 'a t) (pred : int) : unit =
    node.pred <- List.filter ((!=) pred) node.pred

  let structure_without_loops_destructive (node : 'a t) : unit =
    (* recursive protection *)
    let alreadyvisited = ref [] in
    let rec helper (node : 'a t) : unit =
      if List.mem node.id !alreadyvisited then
        ();
      alreadyvisited := node.id :: !alreadyvisited;
      node.succ <- List.filter (fun x -> not (List.mem x.id !alreadyvisited)) node.succ;
      List.iter helper node.succ
    in
    helper node

  let compute_pred (node : 'a t) : unit =
    let rec helper_compute_pred (node : 'a t) : unit =
      List.iter (fun x -> (add_pred x node.id); helper_compute_pred x) node.succ;
    in helper_compute_pred node

  let to_string (node: 'a t) (pp: 'a -> string) =
    let already_visited = ref [] in
    let rec to_string node pp already_visited =
      if List.mem node.id !already_visited then
        ""
      else (
        already_visited := node.id :: !already_visited;
        "node: " ^ string_of_int node.id ^ "\n" ^
        "exp:" ^ pp node.exp ^ "\n" ^
        "succ: [ " ^ List.fold_left (fun acc x -> acc ^ to_string x pp already_visited) "" node.succ ^ "]"
      )
    in to_string node pp already_visited 
end
