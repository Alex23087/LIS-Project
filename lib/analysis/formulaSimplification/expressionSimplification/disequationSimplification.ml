open DataStructures
open DataStructures.Analysis
open NormalForm
open ExpressionSimplificationUtils

let disequation_simplification (formula: NormalForm.t) =
  let disequation_simplification (formula: Formula.t) =
    match formula with
    | Comparison(op, lexpr, rexpr) -> (
      match op with
      | Equals | NotEquals -> formula
      | _ ->
        let vars = Analysis_Utils.get_normal_form_disjoint_identifiers formula in

        if IdentifierSet.is_empty vars then
          let expr = ArithmeticExpression.Operation(BinaryOperator.Minus, lexpr, rexpr) in
          let expr = simplify_expression expr in
          let result =
            match expr, op with
            | Literal(value), LessThan -> value < 0
            | Literal(value), LessOrEqual -> value <= 0
            | Literal(value), GreaterThan -> value > 0
            | Literal(value), GreaterOrEqual -> value >= 0
            | _ -> failwith "unexpected"
          in
          bool_to_formula result
        else if IdentifierSet.cardinal vars = 1 then (
          let var = IdentifierSet.choose vars in
          let lexpr = unpack_simplified_expression lexpr in
          let rexpr = unpack_simplified_expression rexpr in
          match lexpr, rexpr with
          | Some((lmult, _, laddendum)), Some((rmult, _, raddendum)) ->
            let numerator = (raddendum - laddendum) in
            let denominator = (lmult - rmult) in
            let op = if denominator >= 0 then op else invert_binary_comparison op in
            if numerator mod denominator = 0 then
              Formula.Comparison(
                op,
                ArithmeticExpression.Variable(var),
                ArithmeticExpression.Literal( numerator / denominator )
              )
            else
              Formula.Comparison(
                op,
                ArithmeticExpression.Variable(var),
                ArithmeticExpression.Operation(
                  BinaryOperator.Division,
                  ArithmeticExpression.Literal(numerator),
                  ArithmeticExpression.Literal(denominator)
                )
              )
          | _ -> formula
        )
        else
          formula
    )
    | _ -> formula
  in
  let disequation_simplification = apply_expression_simplification disequation_simplification in

  let disjoints = List.map disequation_simplification formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = disequation_simplification