open DataStructures.Analysis
open NormalForm
open ExpressionSimplificationUtils

let simplify_arithmetic_expressions (formula: NormalForm.t) =
  let simplify_formula (conjunct: Formula.t) =
    match conjunct with
    | Comparison(op, lexpr, rexpr) ->
      Formula.Comparison(op, simplify_expression lexpr, simplify_expression rexpr)
    | Allocation(id, expr) ->
      Formula.Allocation(id, simplify_expression expr)
    | _ -> conjunct
  in
  let simplify_formula = apply_expression_simplification simplify_formula in

  let disjoints = List.map simplify_formula formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = simplify_arithmetic_expressions