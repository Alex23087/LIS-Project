open Ast
open AnnotationLogic

let annotate = DataStructures.AnnotatedNode.make

let rec command_expression_to_logic_expression (expr: 'a HeapRegularCommands.ArithmeticExpression.t) (annotation_conversion) =
  let command_boperator_to_logic_boperator (op: HeapRegularCommands.ArithmeticOperation.t) =
    match op with
    | Plus -> BinaryOperator.Plus
    | Minus -> BinaryOperator.Minus
    | Times -> BinaryOperator.Times
    | Division -> BinaryOperator.Division
    | Modulo -> BinaryOperator.Modulo
  in

  let annotation = annotation_conversion expr.annotation in
  match expr.node with
  | Literal(value) ->
    annotate (ArithmeticExpression.Literal(value)) annotation
  | Variable(id) ->
    annotate (ArithmeticExpression.Variable(id)) annotation
  | BinaryOperation(op, lexpr, rexpr) ->
    let lexpr = command_expression_to_logic_expression lexpr annotation_conversion in
    let rexpr = command_expression_to_logic_expression rexpr annotation_conversion in
    let op = command_boperator_to_logic_boperator op in
    annotate (ArithmeticExpression.Operation(op, lexpr, rexpr)) annotation

let rec command_bexpression_to_logic_formula (expr: 'a HeapRegularCommands.BooleanExpression.t) (annotation_conversion) =
  let command_bcomparison_to_logic_bcomparison (op: HeapRegularCommands.BooleanComparison.t) =
    match op with
    | Equal -> BinaryComparison.Equals
    | NotEqual -> BinaryComparison.NotEquals
    | LessThan -> BinaryComparison.LessThan
    | LessOrEqual -> BinaryComparison.LessOrEqual
    | GreaterThan -> BinaryComparison.GreaterThan
    | GreaterOrEqual -> BinaryComparison.GreaterOrEqual
  in
  let command_bcomparison_to_negated_logic_bcomparison (op: HeapRegularCommands.BooleanComparison.t) =
    match op with
    | Equal -> BinaryComparison.Equals
    | NotEqual -> BinaryComparison.NotEquals
    | LessThan -> BinaryComparison.GreaterOrEqual
    | LessOrEqual -> BinaryComparison.GreaterThan
    | GreaterThan -> BinaryComparison.LessOrEqual
    | GreaterOrEqual -> BinaryComparison.LessThan
  in
  let negated_command_bexpression (expr: 'a HeapRegularCommands.BooleanExpression.t) =
    annotate (HeapRegularCommands.BooleanExpression.Not(expr)) expr.annotation
  in

  let annotation = annotation_conversion expr.annotation in
  match expr.node with
  | True ->
    annotate (Formula.True) annotation
  | False ->
    annotate (Formula.False) annotation
  (* Propagate the negation inwards *)
  | Not(subexpr) -> (
    match subexpr.node with
    | True ->
      annotate (Formula.False) annotation
    | False ->
      annotate (Formula.True) annotation
    | Not(_) ->
      command_bexpression_to_logic_formula expr annotation_conversion
    | And(lexpr, rexpr) ->
      let lexpr = command_bexpression_to_logic_formula (negated_command_bexpression lexpr) annotation_conversion in
      let rexpr = command_bexpression_to_logic_formula (negated_command_bexpression rexpr) annotation_conversion in
      annotate (Formula.Or(lexpr, rexpr)) annotation
    | Or(lexpr, rexpr) ->
      let lexpr = command_bexpression_to_logic_formula (negated_command_bexpression lexpr) annotation_conversion in
      let rexpr = command_bexpression_to_logic_formula (negated_command_bexpression rexpr) annotation_conversion in
      annotate (Formula.And(lexpr, rexpr)) annotation
    | Comparison(op, lexpr, rexpr) ->
      let lexpr = command_expression_to_logic_expression lexpr annotation_conversion in
      let rexpr = command_expression_to_logic_expression rexpr annotation_conversion in
      let op = command_bcomparison_to_negated_logic_bcomparison op in
      annotate (Formula.Comparison(op, lexpr, rexpr)) annotation
  )
  | And(lexpr, rexpr) ->
    let lexpr = command_bexpression_to_logic_formula lexpr annotation_conversion in
    let rexpr = command_bexpression_to_logic_formula rexpr annotation_conversion in
    annotate (Formula.And(lexpr, rexpr)) annotation
  | Or(lexpr, rexpr) ->
    let lexpr = command_bexpression_to_logic_formula lexpr annotation_conversion in
    let rexpr = command_bexpression_to_logic_formula rexpr annotation_conversion in
    annotate (Formula.Or(lexpr, rexpr)) annotation
  | Comparison(op, lexpr, rexpr) ->
    let lexpr = command_expression_to_logic_expression lexpr annotation_conversion in
    let rexpr = command_expression_to_logic_expression rexpr annotation_conversion in
    let op = command_bcomparison_to_logic_bcomparison op in
    annotate (Formula.Comparison(op, lexpr, rexpr)) annotation