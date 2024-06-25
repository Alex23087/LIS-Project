open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils
let source = {|<< exists y . ( (y < 0) && (x = (0 - y)) ) >>|}

let expected: LogicFormulas.t =
  test_node (Exists(
    "y",
    test_node (And(
      test_node (Comparison(
        LessThan,
        test_node (Variable "y"),
        test_node (Literal 0)
      )),
      test_node (Comparison(
        Equals,
        test_node (Variable "x"),
        test_node (Operation( Minus, test_node (Literal 0), test_node (Variable "y")))
      ))
    ))
  ))
;;

let%test_unit "test formulae n. 05" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected