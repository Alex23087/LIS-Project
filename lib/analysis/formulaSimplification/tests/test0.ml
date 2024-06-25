open DataStructures.Analysis
open NormalForm
open Base

let%test_unit "test 'p && false = false' simplification" =
  let formula = NormalForm.make_from_formula (
    Formula.And(Formula.False, Formula.Allocation("x", ArithmeticExpression.Literal(1)))
  ) in
  let simplified_formula = FormulaSimplificationBase.simplify_formula formula in
  let expected = NormalForm.make_from_formula Formula.False in
  [%test_eq: Formula.t list] simplified_formula.disjoints expected.disjoints

let%test_unit "test 'p && true = p' simplification" =
  let p = Formula.Allocation("x", ArithmeticExpression.Literal(1)) in
  let formula = NormalForm.make_from_formula (
    Formula.And(Formula.True, p)
  ) in
  let simplified_formula = FormulaSimplificationBase.simplify_formula formula in
  let expected = NormalForm.make_from_formula p in
  [%test_eq: Formula.t list] simplified_formula.disjoints expected.disjoints

let%test_unit "(x -> v && z -> w) * x -> t must be false" =
  let formula = NormalForm.make_from_formula (
    Formula.AndSeparately(
      Formula.And(
        Formula.Allocation("x", ArithmeticExpression.Variable("v")),
        Formula.Allocation("z", ArithmeticExpression.Variable("w"))
      ),
      Formula.Allocation("x", ArithmeticExpression.Variable("t"))
    )
  ) in
  let simplified_formula = FormulaSimplificationBase.simplify_formula formula in
  let expected = NormalForm.make_from_formula Formula.False in
  [%test_eq: Formula.t list] simplified_formula.disjoints expected.disjoints

let%test_unit "test 'p * emp = p' simplification" =
  let p = Formula.Allocation("x", ArithmeticExpression.Literal(1)) in
  let formula = NormalForm.make_from_formula (
    Formula.AndSeparately(p, Formula.EmptyHeap)
  ) in
  let simplified_formula = FormulaSimplificationBase.simplify_formula formula in
  let expected = NormalForm.make_from_formula p in
  [%test_eq: Formula.t list] simplified_formula.disjoints expected.disjoints

let%test_unit "test 'p || false = p' simplification" =
  let p = Formula.Allocation("x", ArithmeticExpression.Literal(1)) in
  let formula = NormalForm.make DataStructures.IdentifierSet.empty [p; Formula.False] {first_id = 0; last_id = 0} in
  let simplified_formula = FormulaSimplificationBase.simplify_formula formula in
  let expected = NormalForm.make_from_formula p in
  [%test_eq: Formula.t list] simplified_formula.disjoints expected.disjoints