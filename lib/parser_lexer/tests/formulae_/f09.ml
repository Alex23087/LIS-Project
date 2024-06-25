open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< (5 != x) * (true && false) >>|}

let expected: LogicFormulas.t =
  test_node (AndSeparately (
    test_node (Comparison (
      NotEquals, test_node (Literal 5), test_node (Variable "x")
    )),
    test_node (And (
      test_node True,
      test_node False
    ))
  ))
;;

let%test_unit "test formulae n. 09" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected