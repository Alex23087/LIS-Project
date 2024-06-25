open DataStructures
open DataStructures.Analysis.NormalForm

let get_variable_from_normal_form_expr (expr: ArithmeticExpression.t) =
  match expr with
  | Variable(id) -> Some(id)
  | _ -> None

let rec substitute_expression_in_formula (formula: Formula.t) (changing_expr: ArithmeticExpression.t) (changed_id: identifier) (renamed_id: identifier) =
  match formula with
  | True | False | EmptyHeap ->
    formula, false
  | Allocation(id, expr) ->
    let expr = substitute_expression_in_expression expr changing_expr changed_id in
    if id = changed_id then
      match get_variable_from_normal_form_expr changing_expr with
      | Some(changing_id) -> Formula.Allocation(changing_id, expr), false
      | None  -> Formula.Allocation(renamed_id, expr), true
    else
      Formula.Allocation(id, expr), false
  | NonAllocated(id) ->
    if id = changed_id then
      match get_variable_from_normal_form_expr changing_expr with
      | Some(changing_id) -> Formula.NonAllocated(changing_id), false
      | None  -> Formula.NonAllocated(renamed_id), true
    else
      formula, false
  | Comparison(op, lexpr, rexpr) ->
    let lexpr = substitute_expression_in_expression lexpr changing_expr changed_id in
    let rexpr = substitute_expression_in_expression rexpr changing_expr changed_id in
    Formula.Comparison(op, lexpr, rexpr), false
  | And(lformula, rformula) ->
    let lformula, lrenamed = substitute_expression_in_formula lformula changing_expr changed_id renamed_id in
    let rformula, rrenamed = substitute_expression_in_formula rformula changing_expr changed_id renamed_id in
    Formula.And(lformula, rformula), lrenamed || rrenamed
  | AndSeparately(lformula, rformula) ->
    let lformula, lrenamed = substitute_expression_in_formula lformula changing_expr changed_id renamed_id in
    let rformula, rrenamed = substitute_expression_in_formula rformula changing_expr changed_id renamed_id in
    Formula.AndSeparately(lformula, rformula), lrenamed || rrenamed
and substitute_expression_in_expression (expr: ArithmeticExpression.t) (changing_expr: ArithmeticExpression.t) (changed_id: identifier) =
  match expr with
  | Literal(_) -> expr
  | Variable(id) ->
    if id = changed_id then
      changing_expr
    else
      expr
  | Operation(op, lexpr, rexpr) ->
    let lexpr = substitute_expression_in_expression lexpr changing_expr changed_id in
    let rexpr = substitute_expression_in_expression rexpr changing_expr changed_id in
    ArithmeticExpression.Operation(op, lexpr, rexpr)