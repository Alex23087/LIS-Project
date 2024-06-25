open DataStructures
open DataStructures.Analysis
open Normalization

open Ast.HeapRegularCommands.HeapAtomicCommand
open Ast.HeapRegularCommands.BooleanExpression
open Ast.HeapRegularCommands.ArithmeticExpression

let convert_command_cfg_annotation (command: Parser.Commands.atomic_t) =
  let make = AnnotatedNode.make in
  let convert_logic_formula (formula: Parser.LogicFormulas.t option) =
    Option.map (fun x -> x |> existential_disjuntive_normal_form |> FormulaSimplification.simplify_formula) formula
  in
  let convert_annotation (annotation: Parser.Commands.annotation): Commands.annotation =
    let formula = convert_logic_formula annotation.logic_formula in
    { position = annotation.position; postcondition = formula }
  in
  let rec convert_expr (expr: Parser.Commands.arithmetic_t) =
    let make = fun x -> make x (convert_annotation expr.annotation) in
    match expr.node with
    | Literal(value) -> make (Literal(value))
    | Variable(id) -> make (Variable(id))
    | BinaryOperation(op, lexpr, rexpr) -> make (BinaryOperation(op, convert_expr lexpr, convert_expr rexpr))
  in
  let rec convert_bexpr (expr: Parser.Commands.boolean_t) =
    let make = fun x -> make x (convert_annotation expr.annotation) in
    match expr.node with
    | True -> make True
    | False -> make False
    | Not(expr) -> make (Not(convert_bexpr expr))
    | Or(lexpr, rexpr) -> make (Or(convert_bexpr lexpr, convert_bexpr rexpr))
    | And(lexpr, rexpr) -> make (And(convert_bexpr lexpr, convert_bexpr rexpr))
    | Comparison(op, lexpr, rexpr) -> make (Comparison(op, convert_expr lexpr, convert_expr rexpr))
  in
  let convert_atomic_command (command: Parser.Commands.atomic_t) =
    let make = fun x -> make x (convert_annotation command.annotation) in
    match command.node with
    | Skip -> make Skip
    | Assignment(id, expr) -> make (Assignment(id, convert_expr expr))
    | NonDet(id) -> make (NonDet(id))
    | Guard(bexpr) -> make (Guard(convert_bexpr bexpr))
    | Allocation(id) -> make (Allocation(id))
    | Free(id) -> make (Free(id))
    | ReadHeap(id, heap_id) -> make (ReadHeap(id, heap_id))
    | WriteHeap(heap_id, expr) -> make (WriteHeap(heap_id, convert_expr expr))
  in
  convert_atomic_command command

let from_ast_commands (commands: Parser.Commands.atomic_t list): CfgBlock.t =
  {
    visit_count = 0;
    precondition = None;
    statements = List.map convert_command_cfg_annotation commands;
  }

let equal_command_expression (cmd_expr: 'a Ast.HeapRegularCommands.ArithmeticExpression.t) (logic_expr: NormalForm.ArithmeticExpression.t) =
  let cmd_expr = Analysis_Utils.command_expression_to_logic_expression cmd_expr (fun _ -> ()) in
  let cmd_expr = Normalization.existential_disjuntive_normal_expr cmd_expr in
  cmd_expr = logic_expr