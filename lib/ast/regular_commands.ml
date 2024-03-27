(**{1 Regular Commands}*)

(**This is the Abstract Syntax Tree which represents the programs we want to analyze.
  The data structure allows to add generic annotations to most of the grammar nodes, which
  in out case will be used to store position information in the source files and logic formulas
  associated to a specific command.

  The following is the grammar definition for our programs: 
  
  - {{! RegularCommands.RegularCommand}RegularCommand} ::= AtomicCommand | RegularCommand; RegularCommand | RegularCommand + RegularCommand | RegularCommand*
  - {{! RegularCommands.AtomicCommand}AtomicCommand} ::= skip | Identifier = ArithmeticExpression | BooleanExpression ?
  - {{! RegularCommands.BooleanExpression}BooleanExpression} ::= True | False | !BooleanExpression | BooleanExpression && BooleanExpression  |  BooleanExpression || BooleanExpression  |  ArithmeticExpression BooleanComparison ArithmeticExpression
  - {{! RegularCommands.BooleanComparison}BooleanComparison} ::= == | != | < | <= | > | >=
  - {{! RegularCommands.ArithmeticExpression}ArithmeticExpression} ::= Int(n) | Identifier | ArithmeticExpression BinaryOperator ArithmeticExpression
  - {{! RegularCommands.ArithmeticOperation}BinaryOperator} ::= + | - | * | / | %
*)
module RegularCommands(Annotation: Base.AnnotationType) = struct
  module AnnotatedNode = Base.AnnotatedNode(Annotation)

  module ArithmeticOperation = struct
    type t =
      | Plus
      | Minus
      | Times
      | Division
      | Modulo
    [@@deriving show]
  end

  module BooleanComparison = struct
    type t =
      | Equal
      | NotEqual
      | LessThan
      | LessOrEqual
      | GreaterThan
      | GreaterOrEqual
    [@@deriving show]
  end

  module ArithmeticExpression = struct
    type t_node =
      | Literal of int
      | Variable of Base.identifier
      | BinaryOperation of ArithmeticOperation.t * t * t
    and t = t_node AnnotatedNode.t
    [@@deriving show]
  end

  module BooleanExpression = struct
    type t_node =
      | True
      | False
      | Not of t
      | And of t * t
      | Or of t * t
      | Comparison of BooleanComparison.t * ArithmeticExpression.t * ArithmeticExpression.t
    and t = t_node AnnotatedNode.t
    [@@deriving show]
  end

  module AtomicCommand = struct
    type t_node =
      | Skip
      | Assignment of Base.identifier * ArithmeticExpression.t
      | Guard of BooleanExpression.t
    and t = t_node AnnotatedNode.t
    [@@deriving show]
  end

  module RegularCommand = struct
    type t_node =
      | Command of AtomicCommand.t
      | Sequence of t * t
      | NondeterministicChoice of t * t
      | Star of t
    and t = t_node AnnotatedNode.t
    [@@deriving show]
  end

  type t = RegularCommand.t
  let pp = RegularCommand.pp
  let show = RegularCommand.show
end