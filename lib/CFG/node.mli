module Node : sig
  type 'a t [@@deriving show]
  val make : 'a -> 'a t list -> 'a t

  (** given a node, compute and set its predecessors and the predecessors of its successors *)
  val compute_pred : 'a t -> unit 

  (** given a node with its successors, returns the number of nodes *)
  val length : 'a t -> int
end

module Hashtbl : sig
  val pp : (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) ->
    Format.formatter -> ('a, 'b) Hashtbl.t -> unit
end

module CFG : sig
  type 'a t [@@deriving show]
  type 'a ht_item [@@deriving show]
  val make : string Node.t -> string t
  
  (** returns the current binding of id in cfg, or raises Not_found if no such binding exists *)
  val get : 'a t -> int -> 'a ht_item

  (** returns the successors identifiers of id in cfg, or raises Not_found if id no exists in cfg *)
  val succ_of : 'a t -> int -> int list

  (** returns the predecessors identifiers of id in cfg, or raises Not_found if id no exists in cfg *)
  val pred_of : 'a t -> int -> int list

  (** returns the expression binded with id in cfg, or raises Not_found if id no exists in cfg *)
  val get_exp : 'a t -> int -> 'a
end