(** Concrete implementation of the Regular Commands, with source-position and logic formula in the annotation.
    
    Note that the logic formula annotates after the command, not before. *)

open Analysis_DataStructures_Base
open Base

include Ast.HeapRegularCommands

type annotation = {
  position: (position [@sexp.opaque]);
  logic_formula: LogicFormulas.t option
}
[@@deriving show, sexp, compare]

type t = annotation Ast.HeapRegularCommands.HeapRegularCommand.t
[@@deriving show, sexp, compare]

type atomic_t = annotation Ast.HeapRegularCommands.HeapAtomicCommand.t
[@@deriving show]

type arithmetic_t = annotation Ast.HeapRegularCommands.ArithmeticExpression.t
[@@deriving show]

type boolean_t = annotation Ast.HeapRegularCommands.BooleanExpression.t
[@@deriving show]

let make_annotation line column (formula : LogicFormulas.t option) : annotation =
  let position = make_position line column in
  {position; logic_formula = formula}

let make_annotation_position position (formula : LogicFormulas.t option) : annotation =
  {position; logic_formula = formula}