open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< ((y -> v) * (x = y)) && (x = v) >>|}

let expected: LogicFormulas.t =
  test_node (And (
    test_node (AndSeparately (
        test_node (Allocation ("y", test_node(Variable "v"))), 
        test_node (Comparison ( Equals, test_node (Variable "x"), test_node (Variable "y")))
    )),
    test_node (Comparison ( Equals, test_node (Variable "x"), test_node (Variable "v")))
  ))
;;


let%test_unit "test formulae n. 12" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected