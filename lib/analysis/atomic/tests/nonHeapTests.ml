open AtomicBase
open Normalization
open DataStructures.Analysis.NormalForm
open Analysis_TestUtils

let%test "weakest precondition on skip" =
  let command = annot_cmd Commands.HeapAtomicCommand.Skip in
  let post_condition =
    annot (PFormula.Exists(
      "x",
      annot (PFormula.NonAllocated("x"))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.NonAllocated("x") :: [] in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["x"]

let%test "weakest precondition on assignment" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.Assignment(
      "x",
      annot_cmd (Commands.ArithmeticExpression.Literal(5))
    ))
  in
  let post_condition = 
    annot (PFormula.Or(
      annot (PFormula.Comparison(
        PBinaryComparison.Equals,
        annot (PArithmeticExpression.Variable("x")),
        annot (PArithmeticExpression.Variable("y"))
      )),
      annot (PFormula.NonAllocated("x"))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.And(
      Formula.NonAllocated("a"),
      Formula.Comparison(
        BinaryComparison.Equals,
        ArithmeticExpression.Variable("a"),
        ArithmeticExpression.Literal(5)
      )
    ) ::
    Formula.Comparison(
      BinaryComparison.Equals,
      ArithmeticExpression.Variable("y"),
      ArithmeticExpression.Literal(5)
    ) :: []
  in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["a"]
  
let%test "weakest precondition on assignment 2" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.Assignment(
      "x",
      annot_cmd (Commands.ArithmeticExpression.BinaryOperation(
        Commands.ArithmeticOperation.Plus,
        annot_cmd (Commands.ArithmeticExpression.Variable("w")),
        annot_cmd (Commands.ArithmeticExpression.Literal(5))
      ))
    ))
  in
  let post_condition = 
    annot (PFormula.Or(
      annot (PFormula.Comparison(
        PBinaryComparison.Equals,
        annot (PArithmeticExpression.Variable("x")),
        annot (PArithmeticExpression.Variable("y"))
      )),
      annot (PFormula.NonAllocated("x"))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.And(
      Formula.NonAllocated("a"),
      Formula.Comparison(
        BinaryComparison.Equals,
        ArithmeticExpression.Variable("a"),
        ArithmeticExpression.Operation(
          BinaryOperator.Plus,
          ArithmeticExpression.Variable("w"),
          ArithmeticExpression.Literal(5)
        )
      )
    ) ::
    Formula.Comparison(
      BinaryComparison.Equals,
      ArithmeticExpression.Variable("w"),
      ArithmeticExpression.Operation(
        BinaryOperator.Plus,
        ArithmeticExpression.Variable("y"),
        ArithmeticExpression.Literal(-5)
      )
    ) :: []
  in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["a"]

let%test "weakest precondition on guard" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.Guard(
      annot_cmd (Commands.BooleanExpression.Not(
        annot_cmd (Commands.BooleanExpression.And(
          annot_cmd (Commands.BooleanExpression.Comparison(
            Commands.BooleanComparison.GreaterThan,
            annot_cmd (Commands.ArithmeticExpression.Variable("x")),
            annot_cmd (Commands.ArithmeticExpression.Literal(17))
          )),
          annot_cmd (Commands.BooleanExpression.True)
        ))
      ))
    ))
  in
  let post_condition =
    annot (PFormula.NonAllocated("y"))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.And(
      Formula.Comparison(
        BinaryComparison.LessThan,
        ArithmeticExpression.Variable("x"),
        ArithmeticExpression.Literal(18)
      ),
      Formula.NonAllocated("y")
    ) :: []
  in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << Exists x. x > y >> x = nondet() << x > y >> *)
let%test "weakest precondition on non deterministic assignment" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.NonDet("x"))
  in
  let post_condition =
    annot (PFormula.Comparison(
      PBinaryComparison.GreaterThan,
      annot (PArithmeticExpression.Variable("x")),
      annot (PArithmeticExpression.Variable("y"))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.Comparison(
      BinaryComparison.GreaterThan,
      ArithmeticExpression.Variable("x"),
      ArithmeticExpression.Variable("y")
    ) :: []
  in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["x"]

(* << x1 != y1 >> y = y1 << y != y1 || x1 != y >> *)
let%test "precondition on assignment from tests [0]" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.Assignment("y",
      annot_cmd (Commands.ArithmeticExpression.Variable("y1"))
    ))
  in
  let post_condition =
    annot (PFormula.Or(
      annot (PFormula.Comparison(
        PBinaryComparison.NotEquals,
        annot (PArithmeticExpression.Variable("y")),
        annot (PArithmeticExpression.Variable("y1"))
      )),
      annot (PFormula.Comparison(
        PBinaryComparison.NotEquals,
        annot (PArithmeticExpression.Variable("x1")),
        annot (PArithmeticExpression.Variable("y"))
      ))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.Comparison(
      BinaryComparison.NotEquals,
      ArithmeticExpression.Variable("x1"),
      ArithmeticExpression.Variable("y1")
    ) :: []
  in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << exists a1. a + x > 9999 && a1 < 1 >> x = a + x << exists a.x > 9999 && a < 1 >> *)
let%test "precondition on assignment from tests [1]" =
  let command =
    annot_cmd (Commands.HeapAtomicCommand.Assignment("x",
      annot_cmd (Commands.ArithmeticExpression.BinaryOperation(
        Commands.ArithmeticOperation.Plus,
        annot_cmd (Commands.ArithmeticExpression.Variable("a")),
        annot_cmd (Commands.ArithmeticExpression.Variable("x"))
      ))
    ))
  in
  let post_condition =
    annot (PFormula.Exists("a",
      annot (PFormula.And(
        annot (PFormula.Comparison(
          PBinaryComparison.GreaterThan,
          annot (PArithmeticExpression.Variable("x")),
          annot (PArithmeticExpression.Literal(9999))
        )),
        annot (PFormula.Comparison(
          PBinaryComparison.LessThan,
          annot (PArithmeticExpression.Variable("a")),
          annot (PArithmeticExpression.Literal(1))
        ))
      ))
    ))
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints =
    Formula.And(
      Formula.Comparison(
        BinaryComparison.GreaterThan,
        ArithmeticExpression.Operation(
          BinaryOperator.Plus,
          ArithmeticExpression.Variable("a"),
          ArithmeticExpression.Variable("x")
        ),
        ArithmeticExpression.Literal(9999)
      ),
      Formula.Comparison(
        BinaryComparison.LessThan,
        ArithmeticExpression.Variable("a1"),
        ArithmeticExpression.Literal(1)
      )
    ) :: []
  in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["a1"]