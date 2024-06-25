(**{1 Heap Regular Commands}*)

(**This is the Abstract Syntax Tree which represents the programs we want to analyze.
  The data structure allows to add generic annotations to most of the grammar nodes, which
  in out case will be used to store position information in the source files and logic formulas
  associated to a specific command.

  The following is the grammar definition for our programs: 
  
  - {{! HeapRegularCommands.HeapRegularCommand}HeapRegularCommand} ::= HeapAtomicCommand | HeapRegularCommand; HeapRegularCommand | HeapRegularCommand + HeapRegularCommand | HeapRegularCommand*
  - {{! HeapRegularCommands.HeapAtomicCommand}HeapAtomicCommand} ::= skip | Identifier = ArithmeticExpression | Identifier = nondet() | BooleanExpression ? | Identifier = alloc() | free(Identifier) | Identifier = \[Identifier\]  | \[Identifier\] = ArithmeticExpression
  - {{! HeapRegularCommands.BooleanExpression}BooleanExpression} ::= True | False | !BooleanExpression | BooleanExpression && BooleanExpression	 |  BooleanExpression || BooleanExpression  |  ArithmeticExpression BooleanComparison ArithmeticExpression
  - {{! HeapRegularCommands.BooleanComparison}BooleanComparison} ::= == | != | < | <= | > | >=
  - {{! HeapRegularCommands.ArithmeticExpression}ArithmeticExpression} ::= Int(n) | Identifier | ArithmeticExpression BinaryOperator ArithmeticExpression
  - {{! HeapRegularCommands.ArithmeticOperation}BinaryOperator} ::= + | - | * | / | %
*)

module HeapRegularCommands = struct
  open Base
  open Ppx_compare_lib.Builtin
  open Sexplib.Std

  module ArithmeticOperation = struct
    type t =
      | Plus
      | Minus
      | Times
      | Division
      | Modulo
    [@@deriving show, sexp, compare]
  end

  module BooleanComparison = struct
    type t =
      | Equal
      | NotEqual
      | LessThan
      | LessOrEqual
      | GreaterThan
      | GreaterOrEqual
    [@@deriving show, sexp, compare]
  end

  module ArithmeticExpression = struct
    type 'a t_node =
      | Literal of int
      | Variable of identifier
      | BinaryOperation of ArithmeticOperation.t * 'a t * 'a t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]
  end

  module BooleanExpression = struct
    type 'a t_node =
      | True
      | False
      | Not of 'a t
      | Or of 'a t * 'a t
      | And of 'a t * 'a t
      | Comparison of BooleanComparison.t * 'a ArithmeticExpression.t * 'a ArithmeticExpression.t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]
  end

  module HeapAtomicCommand = struct
    type 'a t_node =
      | Skip
      | Assignment of identifier * 'a ArithmeticExpression.t
      | NonDet of identifier
      | Guard of 'a BooleanExpression.t
      | Allocation of identifier
      | Free of identifier
      | ReadHeap of identifier * identifier
      | WriteHeap of identifier * 'a ArithmeticExpression.t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]

    let modifiedVariables (command: 'a t) =
      match command.node with
      | Skip                  -> (IdentifierSet.empty)
      | Assignment(id, _)     -> (IdentifierSet.singleton id)
      | NonDet(id)            -> (IdentifierSet.singleton id)
      | Guard(_)              -> (IdentifierSet.empty)
      | Allocation(id)        -> (IdentifierSet.singleton id)
      | Free(_)               -> (IdentifierSet.empty)
      | ReadHeap(id, _)       -> (IdentifierSet.singleton id)
      | WriteHeap(_, _)       -> (IdentifierSet.empty)
  end

  module HeapRegularCommand = struct
    type 'a t_node =
      | Command of 'a HeapAtomicCommand.t
      | Sequence of 'a t * 'a t
      | NondeterministicChoice of 'a t * 'a t
      | Star of 'a t
    and 'a t = ('a t_node, 'a) AnnotatedNode.t
    [@@deriving show, sexp, compare]

    let rec modifiedVariables (command: 'a t) = 
      match command.node with
      | Command(atomicCommand) ->
         HeapAtomicCommand.modifiedVariables atomicCommand
      | NondeterministicChoice(regularCommand1, regularCommand2) ->
         IdentifierSet.union (modifiedVariables regularCommand1) (modifiedVariables regularCommand2)
      | Sequence(regularCommand1, regularCommand2) ->
         IdentifierSet.union (modifiedVariables regularCommand1) (modifiedVariables regularCommand2)
      | Star(regularCommand) ->
         modifiedVariables regularCommand
  end

  type 'a t = 'a HeapRegularCommand.t
  let pp = HeapRegularCommand.pp
  let show = HeapRegularCommand.show
  let t_of_sexp = HeapRegularCommand.t_of_sexp
  let sexp_of_t = HeapRegularCommand.sexp_of_t
  let compare = HeapRegularCommand.compare
  let modifiedVariables = HeapRegularCommand.modifiedVariables
end
