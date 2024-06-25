open Cfg_Node

module CFG = struct
  (* Auxiliary module for providing Hashtbl of a pretty printing function *)
  module Hashtbl = struct
    include Hashtbl

    let pp pp_key pp_value ppf values =
      Hashtbl.iter (fun key data -> Format.fprintf ppf "@[<1>%a: %a@]@." pp_key key pp_value data) values
  end

  (* Stores an immutable variant of the cfg_Node.Node structure *)
  type 'a item = {
    id    : int;
    exp   : 'a;
    pred  : int list;
    succ  : int list;
  } [@@deriving show]

  (** The CFG is implemented as an Hashtable <id, (id, exp, predecessors, successors)>  *)
  type 'a t = {
    cfg: (int, 'a item) Hashtbl.t;
    root_id: int
  }
  [@@deriving show]

  let make_item id exp pred succ : 'a item =
    {id = id; exp = exp; pred = pred; succ = succ}

  (** Starting from a node (the root), builds a CFG *)
  let make (initial_node : 'a Node.t) : 'a t =
    let h = Hashtbl.create (Node.length initial_node) in

    let rec helper_make (node : 'a Node.t) : unit =
      match Hashtbl.find_opt h (Node.get_id node) with
      | Some(_) -> ()
      | None -> (
        (* insert node itself *)
        let id_node_succ = List.map (fun (x : 'a Node.t) : int -> Node.get_id x) (Node.get_succ node) in
        Hashtbl.add h (Node.get_id node) (make_item (Node.get_id node) (Node.get_exp node) (Node.get_pred node) id_node_succ);
        List.iter helper_make (Node.get_succ node)
      )
    in
    helper_make initial_node;
    {cfg = h; root_id = Node.get_id initial_node}

  let get      (cfg : 'a t) (id : int) : 'a item  =
    match Hashtbl.find_opt cfg.cfg id with
    | Some(item) -> item
    | None -> raise (Failure ("CFG.get - Not found - Item id: " ^ string_of_int id))
  let succ_of  (cfg : 'a t) (id : int) : int list = (get cfg id).succ
  let pred_of  (cfg : 'a t) (id : int) : int list = (get cfg id).pred
  let get_data (cfg : 'a t) (id : int) : 'a       = (get cfg id).exp

  let get_id (item : 'a item) : int = item.id

  (** Replace the data inside the node id. *)
  let set_data (cfg : 'a t) (id : int) (expr: 'a) : 'a t =
    let cfg = {cfg = Hashtbl.copy cfg.cfg; root_id = cfg.root_id} in
    let item = get cfg id in
    Hashtbl.replace cfg.cfg id (make_item item.id expr item.pred item.succ);
    cfg

  (** Return the root node. *)
  let root (cfg : 'a t) : 'a item = get cfg cfg.root_id

  (* Auxiliary module used into the fold function *)
  module IntSet = Set.Make (struct
    type t = int
    let compare = compare
  end)

  let map (cfg : 'a t) (fn: 'a -> 'b) : 'b t =
    let convert_item (item: 'a item) =
      make_item item.id (fn item.exp) item.pred item.succ
    in
    let f key value acc = Hashtbl.add acc key (convert_item value); acc in
    let new_cfg = Hashtbl.fold f cfg.cfg (Hashtbl.create (Hashtbl.length cfg.cfg)) in
    {cfg = new_cfg; root_id = cfg.root_id}

  let fold (cfg : 'a t) (fn: 'a t -> 'a item -> 'b -> 'b) (acc: 'b) : 'b =
    (* performs a depth first visit of the graph *)
    let visited = IntSet.empty in
    let to_visit = [ (root cfg).id ] in
    let rec helper_fold (to_visit : int list) (visited : IntSet.t) (acc: 'b) : 'b =
      match to_visit with
      | [] -> acc
      | hd::tl -> (
        let visited = IntSet.add hd visited in
        let successors = List.filter (fun x -> not (IntSet.mem x visited)) (succ_of cfg hd) in
        let acc = fn cfg (get cfg hd) acc in
        helper_fold (successors @ tl) visited acc
      )
    in
    helper_fold to_visit visited acc

  let to_string (cfg: 'a t) (pp: 'a -> string) =
    let int_list_pp list =
      "[ " ^ List.fold_left (fun acc x -> (string_of_int x) ^ " " ^ acc) "" list ^ "]"
    in
    let item_pp key value =
      string_of_int key ^ ": {\n" ^
        "succ: " ^ int_list_pp value.succ ^ "\n" ^
        "pred: " ^ int_list_pp value.pred ^ "\n" ^
        "data: " ^ pp value.exp ^ "}"
    in
    Hashtbl.fold (fun key value acc -> acc ^ "\n" ^ item_pp key value) cfg.cfg ""
end
