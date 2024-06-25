open Cfg_Node

(** The module CFG provides the abstraction of a Control Flow Graph. *)
module CFG : sig
  (** The Control Flow Graph data structure *)
  type 'a t [@@deriving show]

  (** The Control Flow Graph's internal item *)
  type 'a item [@@deriving show]

  (** Given a tree composed of nodes, constructs an actual Control Flow Graph. *)
  val make : 'a Node.t -> 'a t
  
  (** returns the root item of the CFG *)
  val root : 'a t -> 'a item

  (** returns the id of a given item in the CFG *)
  val get_id : 'a item -> int
  
  (** apply a mapping function to all the data items in the CFG, and returns the updated CFG *)
  val map : 'a t -> ('a -> 'b) -> 'b t

  (** recursively fold on all the items in the CFG *)
  val fold : 'a t -> ('a t -> 'a item -> 'b -> 'b) -> 'b -> 'b

  (** returns the current binding of a given node's id in the CFG, or raises Not_found if no such binding exists *)
  val get : 'a t -> int -> 'a item

  (** returns the successors identifiers of a given node's id in the CFG, or raises Not_found if no such id exists *)
  val succ_of : 'a t -> int -> int list

  (** returns the predecessors identifiers of a given node's id in the CFG, or raises Not_found if no such id exists *)
  val pred_of : 'a t -> int -> int list

  (** returns the data structure bound with id in the CFG, or raises Not_found if no such id exists *)
  val get_data : 'a t -> int -> 'a

  (** updates the data structure bound with id in the CFG, or raises Not_found if no such id exists *)
  val set_data : 'a t -> int -> 'a -> 'a t

  val to_string : 'a t -> ('a -> string) -> string
end
