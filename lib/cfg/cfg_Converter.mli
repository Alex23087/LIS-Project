open Ast.HeapRegularCommands
open Cfg_Node

(** The module Converter provides a method [convert], that given an AST, it
    converts it into a CFG composed by nodes from the {{! Cfg.Node}Node} module.
    See {{! Cfg.CFG.make}make} to convert the resulting structure to a CFG.
    If the labeled argument keep_structure is true, only the nodes with the same
    type of HeapAtomicCommand will be in the same output Node, otherwise the exp
    list of each node could be heterogeneous. Defaults to true.
 *)
module Converter : sig
  val convert : ?keep_structure:bool -> 'a HeapRegularCommand.t -> 'a HeapAtomicCommand.t list Node.t
end
