open DataStructures
open DataStructures.Analysis
open NormalForm
open Analysis_Utils
open ExpressionSubstitutionUtils

(** [substitute_expression_in_normalized_formula formula expr id] substitutes every occurrence of
the identifier [id] with the expression [expr] in every expression in the normalized [formula].
*)
let substitute_expression_in_normalized_formula (formula: NormalForm.t) (changing_expr: ArithmeticExpression.t) (changed_id: identifier) =
  let original_id_generator = formula.id_generator in
  let renamed_var, renamed_id_generator = new_variable_name changed_id original_id_generator in
  let id_expr = ArithmeticExpression.Variable(renamed_var) in
  let renamed_equal_formula = Formula.Comparison(BinaryComparison.Equals, id_expr, changing_expr) in
  let substitute_in_disjoint (formula: Formula.t) (disjoints: Formula.t list) (accum_renamed_used: bool) =
    let formula, renamed_used = substitute_expression_in_formula formula changing_expr changed_id renamed_var in
    let formula = if renamed_used then
      Formula.And(formula, renamed_equal_formula)
    else
      formula
    in
    (formula :: disjoints), renamed_used || accum_renamed_used
  in
  let disjoints, renamed_used = List.fold_left (fun (disjoints, renamed_used) x -> substitute_in_disjoint x disjoints renamed_used) ([], false) formula.disjoints in
  let id_generator = if renamed_used then renamed_id_generator else original_id_generator in
  let variables = if renamed_used then IdentifierSet.add renamed_var formula.variables else formula.variables in
  NormalForm.make variables disjoints id_generator

(** [substitute_expression_in_formula formula expr id fresh_id] substitutes every occurrence of
the identifier [id] with the expression [expr] in every expression in the normalized [formula].
It uses the [fresh_id] identifier only if aliases are needed.
*)
let substitute_expression_in_formula (formula: Formula.t) (changing_expr: ArithmeticExpression.t) (changed_id: identifier) (renamed_id: identifier) = 
  let id_expr = ArithmeticExpression.Variable(renamed_id) in
  let renamed_equal_formula = Formula.Comparison(BinaryComparison.Equals, id_expr, changing_expr) in
  let formula, renamed_used = substitute_expression_in_formula formula changing_expr changed_id renamed_id in
  if renamed_used then
    Formula.And(formula, renamed_equal_formula)
  else
    formula