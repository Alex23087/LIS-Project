open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils
let source = {|<< (5 + 5) = 5 && (true) >>|}

let expected: LogicFormulas.t =
  test_node (And (
    test_node (Comparison(
      Equals,
      test_node (Operation(Plus, test_node(Literal 5), test_node (Literal 5))),
      test_node (Literal 5)
    )),
    test_node (True)
  ))

let%test_unit "test formulae n. 06" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected