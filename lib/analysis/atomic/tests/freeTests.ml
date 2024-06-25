open AtomicBase
open Normalization
open DataStructures.Analysis.NormalForm
open Analysis_TestUtils
open DataStructures

(* << Exists v . x -> v >> free(x) << x -/> >> *)
let%test "precondition on free(x), post-condition = << x -/> >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
  let post_condition = annot (PFormula.NonAllocated("x") ) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.Allocation("x", Variable("fresh_var")) :: [] in
  test_expected_bound_variables pre_condition 1 &&
  test_expected_disjoints pre_condition expected_disjoints ["fresh_var"]

(* << false >> free(x) << x -> v >> *)
let%test "precondition on free(x), post-condition = << x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = 
  annot (PFormula.Allocation(
      "x",
      annot (PArithmeticExpression.Variable("v"))
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
IdentifierSet.iter (print_endline) pre_condition.variables;
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> free(x) << y -> v >> *)
let%test "precondition on free(x), post-condition = << y -> v >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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

(* << false >> free(x) << Exists x . x -> v >> *)
let%test "precondition on free(x), post-condition = << Exists x . x -> v >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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

(* << false >> free(x) << false >> *)
let%test "precondition on free(x), post-condition = << false >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
  let post_condition = annot (PFormula.False) in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []

(* << exists v . true * x -> v >> free(x) << true >> *)
let%test "precondition on free(x), post-condition = << true >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
  let post_condition = annot (PFormula.True) in
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

(* << false >> free(x) << emp >> *)
let%test "precondition on free(x), post-condition = << emp >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = annot ( PFormula.EmptyHeap ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> free(x) << emp || emp >> *)
let%test "precondition on free(x), post-condition = << emp || emp >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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

(* << exists w. x -> w >> free(x) << emp || x -> v >> *)
let%test "precondition on free(x), post-condition = << emp || x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> free(x) << emp && x -> v >> *)
let%test "precondition on free(x), post-condition = << emp && x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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

(* << false >> free(x) << emp * x -> v >> *)
let%test "precondition on free(x), post-condition = << emp * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> free(x) << emp * y -> v >> *)
let%test "precondition on free(x), post-condition = << emp * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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

(* << Exists v . x -> v >> free(x) << emp * x -/> >> *)
let%test "precondition on free(x), post-condition = << emp * x -/> >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
let expected_disjoints = Formula.Allocation("x",Variable("v")) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << false >> free(x) << y -> v * x -> v >> *)
let%test "precondition on free(x), post-condition = << y -> v * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = annot (PFormula.False) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.False :: [] 
in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists w . y -> v * x -> w >> free(x) << y -> v * x -/> >> *)
let%test "precondition on free(x), post-condition = << y -> v * x -/> >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.NonAllocated("x")) ,
      annot (
        PFormula.Allocation("y",
        annot (PArithmeticExpression.Variable("v"))
        )
      )      
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = 
  Formula.AndSeparately(
    Formula.Allocation("x",Variable("w")),
    Formula.Allocation("y",Variable("v")) 
  ):: [] 
in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["w"]

(* << false >> free(x) << x -/> * x -> v >> *)
let%test "precondition on free(x), post-condition = << x -/> * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = annot (PFormula.False) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists v . x -> v * true >> free(x) << emp * true >> *)
let%test "precondition on free(x), post-condition = << emp * true >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
let post_condition = 
  annot ( 
    PFormula.AndSeparately(
      annot (PFormula.EmptyHeap),
      annot (PFormula.True)
    )
  ) in
let post_condition = existential_disjuntive_normal_form post_condition in
let pre_condition = compute_precondition command post_condition in
let expected_disjoints = Formula.AndSeparately(
    Formula.Allocation("x", Variable("v")),
    Formula.True
  ) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["v"]

(* << false >> free(x) << true * x -> v >> *)
let%test "precondition on free(x), post-condition = << true * x -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
let expected_disjoints = 
  Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << Exists w . x -> w * true * y -> v >> free(x) << true * y -> v >> *)
let%test "precondition on free(x), post-condition = << true * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
      Formula.Allocation("x", Variable("w")),
      Formula.Allocation("y", Variable("v"))
    )) :: [] in
test_expected_bound_variables pre_condition 1 &&
test_expected_disjoints pre_condition expected_disjoints ["w"]

(* << false >> free(x) << v = 5 * x -> v * y -> v >> *)
let%test "precondition on free(x), post-condition = << v = 5 * x -> v * y -> v >>" =
let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
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
let expected_disjoints = Formula.False :: [] in
test_expected_bound_variables pre_condition 0 &&
test_expected_disjoints pre_condition expected_disjoints []

(* << false >> free(x) << Exists x . x -/> * v = 5 >> *)
let%test "precondition on free(x), post-condition = << Exists x . x -/> * v = 5 >>" =
  let command = annot_cmd (Commands.HeapAtomicCommand.Free("x")) in
  let post_condition =
    annot (PFormula.AndSeparately(
      annot (PFormula.Exists("x", 
        annot (PFormula.NonAllocated("x"))
      ) ),
      annot (PFormula.Allocation("v", (annot (PArithmeticExpression.Literal(5) ) ) ) )
    ) )
  in
  let post_condition = existential_disjuntive_normal_form post_condition in
  let pre_condition = compute_precondition command post_condition in
  let expected_disjoints = Formula.False :: [] in
  test_expected_bound_variables pre_condition 0 &&
  test_expected_disjoints pre_condition expected_disjoints []