open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< n * 2 < (1 + 2) - (3 / 4) >>|}

let expected: LogicFormulas.t = 
  test_node (Comparison (
    LessThan,
    test_node (Operation (
      Times, test_node (Variable "n"), test_node (Literal 2)
    )),
    test_node (Operation (
      Minus,
      test_node (Operation (Plus, test_node (Literal 1), test_node (Literal 2))),
      test_node (Operation (Division, test_node (Literal 3), test_node (Literal 4)))
    ))
  ))
;;

let%test_unit "test formulae n. 10" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected