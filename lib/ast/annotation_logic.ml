(**{1 Annotation Logic}*)

(**This is the Abstract Syntax Tree which represents the logic formulas used to annotate our programs.
  The data structure allows to add generic annotations to most of the grammar nodes, which
  in out case will be used to store position information in the source files.

  The following is the grammar definition for our programs:
  - {{! AnnotationLogic.Formula}Formula} ::= True | False | Exists Identifier . Formula | Formula && Formula | Formula || Formula | ArithmeticExpression BinaryComparison ArithmeticExpression | Emp | x -> ArithmeticExpression | x -/> | Formula * Formula
  - {{! AnnotationLogic.BinaryComparison}BinaryComparison} ::= < | > | <= | >= | = | !=
  - {{! AnnotationLogic.ArithmeticExpression}ArithmeticExpression} ::= Int(n) | Identifier | ArithmeticExpression BinaryOperator ArithmeticExpression
  - {{! AnnotationLogic.BinaryOperator}BinaryOperator} ::= + | - | * | / | %
*)

module AnnotationLogic = struct
  open Base
  open Sexplib.Std
  open Ppx_compare_lib.Builtin

  module BinaryOperator = struct
    type t =
      | Plus
      | Minus
      | Times
      | Division
      | Modulo
    [@@deriving show, sexp, compare, eq]
  end

  module ArithmeticExpression = struct
    type 'a t_node =
      | Literal of int
      | Variable of identifier
      | Operation of BinaryOperator.t * 'a t * 'a t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]
  end

  module BinaryComparison = struct
    type t =
      | LessThan
      | GreaterThan
      | LessOrEqual
      | GreaterOrEqual
      | Equals
      | NotEquals
    [@@deriving show, sexp, compare, eq]
  end

  module Formula = struct
    type 'a t_node =
      | True
      | False
      | Exists of identifier * 'a t
      | And of 'a t * 'a t
      | Or of 'a t * 'a t
      | Comparison of BinaryComparison.t * 'a ArithmeticExpression.t * 'a ArithmeticExpression.t

      (* Spatial Formulas *)
      | EmptyHeap
      | NonAllocated of identifier
      | Allocation of identifier * 'a ArithmeticExpression.t
      | AndSeparately of 'a t * 'a t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]
  end

  type 'a t = 'a Formula.t
  let pp = Formula.pp
  let show = Formula.show
  let t_of_sexp = Formula.t_of_sexp
  let sexp_of_t = Formula.sexp_of_t
  let compare = Formula.compare
end
