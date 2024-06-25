open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< exists n . ((0 + n >= 20000) && (n > 0))>>|}

let expected: LogicFormulas.t =
  test_node (Exists(
    "n",
    test_node (And(
      test_node (Comparison(
        GreaterOrEqual,
        test_node (Operation (Plus, test_node (Literal 0), test_node (Variable "n"))),
        test_node (Literal 20000))),
      test_node (Comparison(
        GreaterThan,
        test_node (Variable "n"),
        test_node (Literal 0)))
    ))
  ))

;;

let%test_unit "test formulae n. 14" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected