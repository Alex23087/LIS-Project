module Node : sig
  type 'a t [@@deriving show, sexp, compare]
  val make : 'a -> 'a t list -> int list -> 'a t

  val getnodeid : 'a t -> int

  val getexp : 'a t -> 'a

  (** given a node with its successors, returns the number of nodes *)
  val length : 'a t -> int

  val addsucc : 'a t -> 'a t -> unit

  val setsucc : 'a t -> 'a t list -> unit

  val replaceexp : 'a t -> 'a -> unit

  val structure_without_loops_destructive : 'a t -> unit

  val succ : 'a t -> 'a t list

  val prev : 'a t -> int list
end

module CFG : sig
  (** The Control Flow Graph data structure *)
  type 'a t [@@deriving show]

  (** The Control Flow Graph's internal item *)
  type 'a item [@@deriving show]
  val make : 'a Node.t -> 'a t
  
  (** returns the root item of the CFG *)
  val root : 'a t -> 'a item

  (** returns the index of a given item in the CFG *)
  val idx : 'a t -> 'a item -> int

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
end
