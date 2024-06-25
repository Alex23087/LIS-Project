include RenameVariable
include NormalFormUtils
include CommandToLogicConversion

module Print = PrintUtils
open DataStructures
open Parser
open LogicFormulas

let annotate = DataStructures.AnnotatedNode.make

let first_annotation (annot1: LogicFormulas.annotation) (annot2: LogicFormulas.annotation) =
  if annot1.position.line < annot2.position.line then
    annot1
  else if annot1.position.line > annot2.position.line then
    annot2
  else if annot1.position.column <= annot2.position.column then
    annot1
  else
    annot2

(* https://stackoverflow.com/a/10893700 *)
let list_cartesian l l' =
  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)
    
let get_variable_from_expression (expr: 'a ArithmeticExpression.t) =
  match expr.node with
  | Variable(id) -> Some(id)
  | _ -> None

let command_annotation_to_logic_annotation (annotation: Commands.annotation) : annotation =
  {position=annotation.position}
    
let rec get_expr_identifiers (expr: 'a ArithmeticExpression.t) =
  match expr.node with
  | Literal(_) -> (IdentifierSet.empty)
  | Variable(id) -> (IdentifierSet.singleton id)
  | Operation(_, lexpr, rexpr) ->
    let l_ids = get_expr_identifiers lexpr in
    let r_ids = get_expr_identifiers rexpr in
    IdentifierSet.union l_ids r_ids

let identifier_in_expr (expr: 'a ArithmeticExpression.t) (id: identifier) =
  let identifiers = get_expr_identifiers expr in
  IdentifierSet.exists (fun x -> String.equal id x) identifiers

let rec get_formula_identifiers (formula: 'a Formula.t) =
  match formula.node with
  | True | False | EmptyHeap ->
    IdentifierSet.empty
  | Allocation(id, _) | NonAllocated(id) ->
    IdentifierSet.singleton id
  | Comparison(_, lexpr, rexpr) ->
    IdentifierSet.union (get_expr_identifiers lexpr) (get_expr_identifiers rexpr)
  | And(lformula, rformula) | AndSeparately(lformula, rformula) ->
    IdentifierSet.union (get_formula_identifiers lformula) (get_formula_identifiers rformula)
  | Exists(_, _) ->
    raise (Failure "Formulas of existential abstraction cannot be contained in normal form disjoints")
  | Or(_, _) ->
    raise (Failure "Disjunction of formulas cannot be contained in normal form disjoints")
