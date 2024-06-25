open AtomicBase
open Normalization
open DataStructures.Analysis.NormalForm
open Analysis_TestUtils

(* << Exists v . x -> v >> [x] := y << x -> y >> *)
let%test "precondition on [x] := y, post-condition = << x -> y >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
      )
    ) in
  let post_condition =
    annot (PFormula.Allocation(
      "x",
      annot (PArithmeticExpression.Variable("y"))
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.Allocation("x", Variable("fresh")) :: [] in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["fresh"]

(* << Exists v . x -> v >> [x] := 5 + 5 << x -> 5 + 5 >> *)
let%test "precondition on [x] := 5+5, post-condition = << x -> 5+5 >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (
        Commands.ArithmeticExpression.BinaryOperation(
          Commands.ArithmeticOperation.Plus, 
            (annot_cmd (Commands.ArithmeticExpression.Literal(5))), 
            (annot_cmd (Commands.ArithmeticExpression.Literal(5)))
          )
        )
      )
    )
  ) in
  let post_condition =
    annot (
      PFormula.Allocation(
        "x",
        annot (
          PArithmeticExpression.Operation(
            PBinaryOperator.Plus,
            annot (PArithmeticExpression.Literal(5)),
            annot (PArithmeticExpression.Literal(5))
          )
        )
      )
    ) 
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.Allocation("x", Variable("v")) :: [] in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << False >> [x] := 5 + 5 << x -> 5 + 7 >> *)
let%test "precondition on [x] := 5+5, post-condition = << x -> 5+7 >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (
        Commands.ArithmeticExpression.BinaryOperation(
          Commands.ArithmeticOperation.Plus, 
            (annot_cmd (Commands.ArithmeticExpression.Literal(5))), 
            (annot_cmd (Commands.ArithmeticExpression.Literal(5)))
          )
        )
      )
    )
  ) in
  let post_condition =
    annot (
      PFormula.Allocation(
        "x",
        annot (
          PArithmeticExpression.Operation(
            PBinaryOperator.Plus,
            annot (PArithmeticExpression.Literal(5)),
            annot (PArithmeticExpression.Literal(7))
          )
        )
      )
    ) 
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << x -/> v >> *)
let%test "precondition on [x] := y, post-condition = << x -/> >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = annot ( PFormula.NonAllocated("x") ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << y -> v >> *)
let%test "precondition on [x] := y, post-condition = << y -> v >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition =
    annot (PFormula.Allocation(
      "y",
      annot (PArithmeticExpression.Variable("v"))
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << Exists x . x -> v >> *)
let%test "precondition on [x] := y, post-condition = << Exists x . x -> v >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition =
    annot (PFormula.Exists("x", 
      annot (PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("v"))
        )
      )
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << Exists x . x -> y >> *)
let%test "precondition on [x] := y, post-condition = << Exists x . x -> y >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition =
    annot (PFormula.Exists("x", 
      annot (PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
        )
      )
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << Exists y . x -> y >> *)
let%test "precondition on [x] := y, post-condition = << Exists y . x -> y >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition =
    annot (PFormula.Exists("y", 
      annot (PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
        )
      )
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << false >> *)
let%test "precondition on [x] := y, post-condition = << false >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition = annot (PFormula.False) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << true >> [x] := y << true >> *)
let%test "precondition on [x] := y, post-condition = << true >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition = annot (PFormula.True) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.True :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << emp >> *)
let%test "precondition on [x] := y, post-condition = << emp >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = annot ( PFormula.EmptyHeap ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << emp || emp >> *)
let%test "precondition on [x] := y, post-condition = << emp || emp >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.Or(
      annot (PFormula.EmptyHeap),
      annot (PFormula.EmptyHeap)
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists v . x -> v >> [x] := y << emp || x -> y >> *)
let%test "precondition on [x] := y, post-condition = << emp || x -> y >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.Or(
      annot (PFormula.EmptyHeap),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.Allocation("x", Variable("fresh")) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["fresh"]

(* << false >> [x] := y << emp && x -> v >> *)
let%test "precondition on [x] := y, post-condition = << emp && x -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.And(
      annot (PFormula.EmptyHeap),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(***************************** Frame Rule *********************************)

(* << Exists v . x -> v >> [x] := y << emp * x -> y >> *)
let%test "precondition on [x] := y, post-condition = << emp * x -> y >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.Allocation("x", Variable("v")) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << false >> [x] := y << emp * y -> v >> *)
let%test "precondition on [x] := y, post-condition = << emp * y -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (
        PFormula.Allocation(
        "y",
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << emp * x -/> >> *)
let%test "precondition on [x] := y, post-condition = << emp * x -/> >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (
        PFormula.NonAllocated("x")
      )
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists w . y -> v * x -> w >> [x] := y << y -> v * x -> y >> *)
let%test "precondition on [x] := y, post-condition = << y -> v * x -> y >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (
        PFormula.Allocation(
        "y",
        annot (PArithmeticExpression.Variable("v"))
      )),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.AndSeparately(
    Formula.Allocation("y", Variable("v")),
    Formula.Allocation("x", Variable("w"))
  )
   :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["w"]

(* << false >> [x] := y << x -/> * x -> v >> *)
let%test "precondition on [x] := y, post-condition = << x -/> * x -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.NonAllocated("x")),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> [x] := y << x -/> * x -> y >> *)
let%test "precondition on [x] := y, post-condition = << x -/> * x -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.NonAllocated("x")),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists v . x -> v * true >> [x] := y << emp * true >> *)
let%test "precondition on [x] := y, post-condition = << emp * true >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (PFormula.True)
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints =
  Formula.AndSeparately(
    Formula.True, 
    Formula.Allocation("x", Variable("v"))
  ) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << Exists v . true * x -> v >> [x] := y << true * x -> y >> *)
let%test "precondition on [x] := y, post-condition = << true * x -> y >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.True),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("y"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.AndSeparately(
    Formula.True,
    Formula.Allocation("x", Variable("v"))
  )
  :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << Exists w . true * y -> v * x -> w >> [x] := y << true * y -> v >> *)
let%test "precondition on [x] := y, post-condition = << true * y -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.True),
      annot (
        PFormula.Allocation(
        "y",
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.AndSeparately(
    Formula.True,
    Formula.AndSeparately(
      Formula.Allocation("y", Variable("v")),
      Formula.Allocation("x", Variable("w"))
    )
  ) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["w"]

(* << false >> [x] := y << v = 5 * x -> v * y -> v >> *)
let%test "precondition on [x] := y, post-condition = << v = 5 * x -> v * y -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.Allocation("v", (annot (PArithmeticExpression.Literal(5) ) ) ) ),
      annot (PFormula.AndSeparately(
        annot (PFormula.Allocation("x", annot (PArithmeticExpression.Variable("v") ) ) ),
        annot (PFormula.Allocation("y", annot (PArithmeticExpression.Variable("v") ) ) ) 
      )
    ))
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.False:: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists w . x -> w * v = 5 * y -> v >> [x] := y << v = 5 * x -> y * y -> v >> *)
let%test "precondition on [x] := y, post-condition = << v = 5 * x -> y * y -> v >>" =
let command = annot_cmd (
  Commands.HeapAtomicCommand.WriteHeap("x", 
    (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
  )
) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.Allocation("v", (annot (PArithmeticExpression.Literal(5) ) ) ) ),
      annot (PFormula.AndSeparately(
        annot (PFormula.Allocation("x", annot (PArithmeticExpression.Variable("y") ) ) ),
        annot (PFormula.Allocation("y", annot (PArithmeticExpression.Variable("v") ) ) ) 
      )
    ))
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.AndSeparately(
    Formula.Allocation("v", Literal(5)),
    Formula.AndSeparately(
      Formula.Allocation("x", Variable("w")),
      Formula.Allocation("y", Variable("v"))
    )
  ) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["w"]

(* << false >> [x] := y << Exists x . x -> y * v = 5 >> *)
let%test "precondition on [x] := y, post-condition = << Exists x . x -> y * v = 5 >>" =
  let command = annot_cmd (
    Commands.HeapAtomicCommand.WriteHeap("x", 
      (annot_cmd (Commands.ArithmeticExpression.Variable("y")))
    )
  ) in
  let post_condition =
    annot (PFormula.AndSeparately(
      annot (PFormula.Exists("x", 
        annot (PFormula.Allocation(
          "x",
          annot (PArithmeticExpression.Variable("y"))
          )
        )
      ) ),
      annot (PFormula.Allocation("v", (annot (PArithmeticExpression.Literal(5) ) ) ) )
    ) )
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []