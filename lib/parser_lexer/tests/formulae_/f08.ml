open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< exists n . exists m . 5 % n = m >>|}

let expected: LogicFormulas.t =
  test_node ( Exists (
    "n",
    test_node ( Exists (
      "m",
      test_node (Comparison (
        Equals,
        test_node (Operation ( Modulo, test_node (Literal 5), test_node (Variable "n"))),
        test_node (Variable "m")
      ))
    ))
  ))
;;

let%test_unit "test formulae n. 08" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected