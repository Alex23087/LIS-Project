open AtomicBase
open Normalization
open DataStructures.Analysis.NormalForm
open Analysis_TestUtils

(* << emp >> x := alloc() << x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << x -> v >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
  let post_condition =
    annot (PFormula.Allocation(
      "x",
      annot (PArithmeticExpression.Variable("v"))
    )
  ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.EmptyHeap :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << x -/> >> *)
let%test "precondition on x := alloc(), post-condition = << x -/> >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = annot ( PFormula.NonAllocated("x") ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << y -> v >> *)
let%test "precondition on x := alloc(), post-condition = << y -> v >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << false >> x := alloc() << Exists x . x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << Exists x . x -> v >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << false >> x := alloc() << false >> *)
let%test "precondition on x := alloc(), post-condition = << false >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
  let post_condition = annot (PFormula.False) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << true >> x := alloc() << true >> *)
let%test "precondition on x := alloc(), post-condition = << true >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
  let post_condition = annot (PFormula.True) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.True :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << emp >> *)
let%test "precondition on x := alloc(), post-condition = << emp >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = annot ( PFormula.EmptyHeap ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << emp || emp >> *)
let%test "precondition on x := alloc(), post-condition = << emp || emp >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << emp >> x := alloc() << emp || x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << emp || x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = 
  annot ( 
    PFormula.Or(
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
let expected_disjoints = Formula.EmptyHeap :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << emp && x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << emp && x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << emp >> x := alloc() << emp * x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << emp * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
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
let expected_disjoints = Formula.EmptyHeap :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << emp * y -> v >> *)
let%test "precondition on x := alloc(), post-condition = << emp * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << false >> x := alloc() << emp * x -/> >> *)
let%test "precondition on x := alloc(), post-condition = << emp * x -/> >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << y -> v >> x := alloc() << y -> v * x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << y -> v * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.Allocation("y", Variable("v")) :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << x -/> * x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << x -/> * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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

(* << true >> x := alloc() << emp * true >> *)
let%test "precondition on x := alloc(), post-condition = << emp * true >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (PFormula.True)
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.True :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << true >> x := alloc() << true * x -> v >> *)
let%test "precondition on x := alloc(), post-condition = << true * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.True),
      annot (
        PFormula.Allocation(
        "x",
        annot (PArithmeticExpression.Variable("v"))
      ))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.True :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << true * false >> x := alloc() << true * y -> v >> *)
let%test "precondition on x := alloc(), post-condition = << true * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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
  Formula.AndSeparately(Formula.True, Formula.Allocation("y", Variable("v"))) :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << v = 5 * y -> v >> x := alloc() << v = 5 * x -> v * y -> v >> *)
let%test "precondition on x := alloc(), post-condition = << v = 5 * x -> v * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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
  Formula.AndSeparately(
    Formula.Allocation("v", Literal(5)), 
    Formula.Allocation("y", Variable("v"))
  ) :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* Test commutativity *)
(* << v = 5 * y -> v >> x := alloc() << v = 5 * x -> v * y -> v >> *)
let%test "precondition on x := alloc(), post-condition = << v = 5 * x -> v * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
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
  Formula.AndSeparately(
    Formula.Allocation("y", Variable("v")),
    Formula.Allocation("v", Literal(5))
  ) :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> x := alloc() << Exists x . x -> v * v = 5 >> *)
let%test "precondition on x := alloc(), post-condition = << Exists x . x -> v * v = 5 >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Allocation("x")) in
  let post_condition =
    annot (PFormula.AndSeparately(
      annot (PFormula.Exists("x", 
        annot (PFormula.Allocation(
          "x",
          annot (PArithmeticExpression.Variable("v"))
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