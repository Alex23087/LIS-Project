open DataStructures
open DataStructures.Analysis
open NormalForm
open Submodules

let unpack_comparison (formula: Formula.t) =
  match formula with
  | Comparison(op, lexpr, rexpr) -> (op, lexpr, rexpr)
  | _ -> raise (Failure "unexpected")

let rec unpack_conjuncts (formula: Formula.t) =
  match formula with
  | Comparison(_) -> [formula], []
  | And(lformula, rformula) ->
    let lcomparisons, lothers = unpack_conjuncts lformula in
    let rcomparisons, rothers = unpack_conjuncts rformula in
    lcomparisons @ rcomparisons, lothers @ rothers
  | _ -> [], [formula]

let rec pack_conjuncts (formulas: Formula.t list) =
  match formulas with
  | [] -> failwith "unexpected"
  | [x] -> x
  | x::xs -> Formula.And(x, pack_conjuncts xs)


let unpack_simplified_expression (expr: ArithmeticExpression.t) =
  match expr with
  | ArithmeticExpression.Operation(op, lexpr, rexpr) -> (
    match op, lexpr, rexpr with
    | Plus, Variable(var), Literal(addendum) -> 
      Some((1, var, addendum))
    | Minus, Variable(var), Literal(addendum) -> 
      Some((1, var, -addendum))
    | Plus, Operation(Times, Literal(multiplier), Variable(var)), Literal(addendum) -> 
      Some((multiplier, var, addendum))
    | Minus, Operation(Times, Literal(multiplier), Variable(var)), Literal(addendum) -> 
      Some((multiplier, var, -addendum))
    | Times, Literal(multiplier), Variable(var) ->
      Some((multiplier, var, 0))
    | _ -> None
  )
  | Literal(value) -> Some((0, "", value))
  | Variable(var) -> Some((1, var, 0))

let bool_to_formula bool = if bool then Formula.True else Formula.False

let invert_binary_comparison (op: BinaryComparison.t) =
  match op with
  | LessOrEqual -> BinaryComparison.GreaterOrEqual
  | LessThan -> BinaryComparison.GreaterThan
  | GreaterThan -> BinaryComparison.LessThan
  | GreaterOrEqual -> BinaryComparison.LessOrEqual
  | _  -> op

let rec has_modulo_operator (expr: ArithmeticExpression.t) =
  match expr with
  | Operation(op, lexpr, rexpr) ->
    op = BinaryOperator.Modulo || has_modulo_operator lexpr || has_modulo_operator rexpr
  | _ -> false

let to_symalg_operator (op: BinaryOperator.t) =
  match op with
  | Plus -> SymAlg.Plus
  | Minus -> SymAlg.Minus
  | Times -> SymAlg.Times
  | Division -> SymAlg.Div
  | Modulo -> raise (Failure "SymAlg does not support the modulo operator")

let rec to_symalg_expression (expr: ArithmeticExpression.t) =
  match expr with
  | Literal(value) ->
    SymAlg.Leaf(SymAlg.Poly([ (float_of_int value, []) ]))
  | Variable(id) ->
    SymAlg.Leaf(SymAlg.Poly([ (1., [(id, 1.)]) ]))
  | Operation(op, lexpr, rexpr) -> (
    let op = to_symalg_operator op in
    let lexpr = to_symalg_expression lexpr in
    let rexpr = to_symalg_expression rexpr in
    SymAlg.Node(op, [lexpr; rexpr])
  )

let to_symalg_equation ((lexpr, rexpr) : ArithmeticExpression.t * ArithmeticExpression.t) = 
  (to_symalg_expression lexpr, to_symalg_expression rexpr)

let from_symalg_operator (op: SymAlg.operator) =
  match op with
  | Plus -> BinaryOperator.Plus
  | Minus -> BinaryOperator.Minus
  | Times -> BinaryOperator.Times
  | Div -> BinaryOperator.Division
  | Power -> raise (Failure "Our logic does not support the power operator")

let rec from_symalg_power ((var, power): SymAlg.power) =
  let power = int_of_float power in
  if power = 0 then
    ArithmeticExpression.Literal(1)
  else if power = 1 then
    ArithmeticExpression.Variable(var)
  else if power > 1 then
    ArithmeticExpression.Operation(
      BinaryOperator.Times,
      ArithmeticExpression.Variable(var),
      from_symalg_power (var, float_of_int (power - 1))
    )
  else (* power < 0 *)
    ArithmeticExpression.Operation(
      BinaryOperator.Division,
      ArithmeticExpression.Literal(1),
      from_symalg_power (var, float_of_int (-power))
    )

let rec from_symalg_power_list (power_list: SymAlg.power list) =
  match power_list with
  | [] -> ArithmeticExpression.Literal(1)
  | [x] -> from_symalg_power x
  | x::xs -> 
    ArithmeticExpression.Operation(
      BinaryOperator.Times,
      from_symalg_power x,
      from_symalg_power_list xs
    )

let from_symalg_mono ((mult, power_list): SymAlg.monomial) =
  let mult = int_of_float mult in
  let mult_literal = ArithmeticExpression.Literal(mult) in
  if mult = 0 then
    mult_literal
  else if mult = 1 then
    from_symalg_power_list power_list
  else if List.length power_list = 0 then
    mult_literal
  else
    ArithmeticExpression.Operation(
      BinaryOperator.Times,
      mult_literal,
      from_symalg_power_list power_list
    )

let rec from_symalg_poly (poly: SymAlg.polynomial) =
  match poly with
  | [] -> ArithmeticExpression.Literal(0)
  | [x] -> from_symalg_mono x
  | x::xs -> 
    ArithmeticExpression.Operation(
      BinaryOperator.Plus,
      from_symalg_mono x,
      from_symalg_poly xs
    )

let from_symalg_frac ((numerator, denominator): SymAlg.frac) =
  ArithmeticExpression.Operation(
    BinaryOperator.Division,
    from_symalg_poly numerator,
    from_symalg_poly denominator
  )

let from_symalg_term (term: SymAlg.term) =
  match term with
  | Poly(poly) -> from_symalg_poly poly
  | Frac(frac) -> from_symalg_frac frac
  | Exp(_) -> raise (Failure "Our logic does not support exponentiation")

let rec from_symalg_expression (expr: SymAlg.expr) =
  match expr with
  | Node(op, exprs) -> (
    match exprs with
    | [] -> (
      match op with
      | Plus | Minus -> ArithmeticExpression.Literal(0)
      | Times | Div -> ArithmeticExpression.Literal(1)
      | Power -> raise (Failure "Our logic does not support exponentiation")
    )
    | [x] -> from_symalg_expression x
    | x::xs -> 
      ArithmeticExpression.Operation(
        from_symalg_operator op,
        from_symalg_expression x,
        from_symalg_expression (SymAlg.Node(op, xs))
      )
  )
  | Leaf(term) -> from_symalg_term term

let from_symalg_equation ((lexpr, rexpr): SymAlg.eqn) =
  (from_symalg_expression lexpr, from_symalg_expression rexpr)

let simplify_expression (expr: ArithmeticExpression.t) =
  let simplify_symalg expr =
    expr |> to_symalg_expression
         |> SymAlg.simplify_expr
         |> from_symalg_expression
  in
  let rec simplify_expression (expr: ArithmeticExpression.t) =
    match expr with
    | Operation(op, expr1, expr2) ->
      let expr1, modulo_in_1 = simplify_expression expr1 in
      let expr2, modulo_in_2 = simplify_expression expr2 in
      if modulo_in_1 || modulo_in_2 || op = BinaryOperator.Modulo then
        ArithmeticExpression.Operation(op, expr1, expr2), true
      else
        let expr = ArithmeticExpression.Operation(op, expr1, expr2) in
        let expr = simplify_symalg expr in
        expr, false
    | _ ->
      expr, false
  in
  simplify_expression expr |> fst

let simplify_equation (lexpr: ArithmeticExpression.t) (rexpr: ArithmeticExpression.t) (var: identifier) =
  if has_modulo_operator lexpr || has_modulo_operator rexpr then
    (lexpr, rexpr)
  else
    (lexpr, rexpr) |> to_symalg_equation
                   |> (fun x -> SymAlg.solve x var)
                   |> from_symalg_equation

let rec apply_expression_simplification (f: Formula.t -> Formula.t) (formula: Formula.t) =
  match formula with
  | Comparison(_) | Allocation(_) ->
    f formula
  | And(lformula, rformula) ->
    let lformula = apply_expression_simplification f lformula in
    let rformula = apply_expression_simplification f rformula in
    Formula.And(lformula, rformula)
  | AndSeparately(lformula, rformula) ->
    let lformula = apply_expression_simplification f lformula in
    let rformula = apply_expression_simplification f rformula in
    Formula.AndSeparately(lformula, rformula)
  | _ -> formula
