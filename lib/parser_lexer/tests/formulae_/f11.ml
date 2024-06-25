open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< (y -> v) * (v = x) >>|}

let expected: LogicFormulas.t = 
  test_node (AndSeparately (
    test_node (Allocation ("y", test_node (Variable "v"))),
    test_node (Comparison (Equals, test_node (Variable "v"), test_node(Variable "x")))
  ))
;;

let%test_unit "test formulae n. 11" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected