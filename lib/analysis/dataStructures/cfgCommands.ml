open Analysis_DataStructures_Base
open NormalizedFormulas

(** Commands for CFG

The commands' data structures update their annotation to use normalized formulas when used in the Control Flow Graph.
*)
module Commands = struct
  type annotation = {
    position: position;
    postcondition: NormalForm.t option;
  }
  [@@deriving show]

  type t = annotation Ast.HeapRegularCommands.HeapAtomicCommand.t
  [@@deriving show]

  type boolean_t = annotation Ast.HeapRegularCommands.BooleanExpression.t
  [@@deriving show]

  type arithmetic_t = annotation Ast.HeapRegularCommands.ArithmeticExpression.t
  [@@deriving show]

  let get_postcondition (command: ('a, annotation) AnnotatedNode.t) =
    command.annotation.postcondition

  let update_postcondition (command: ('a, annotation) AnnotatedNode.t) postcondition =
    let annotation = {
      position = command.annotation.position;
      postcondition
    } in
    AnnotatedNode.update_annotation command annotation
end