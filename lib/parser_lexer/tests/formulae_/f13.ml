open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< (exists a . v -> z) * ( (z = a) * ( true * ( (exists b . a -> b) * ( (x = a) || (x -/>) ) ) ) ) >>|}

let expected: LogicFormulas.t =
  test_node ( AndSeparately (
    test_node ( Exists ("a", test_node (Allocation ("v", test_node (Variable "z"))))),
    test_node ( AndSeparately (
      test_node (Comparison (Equals, test_node (Variable "z"), test_node (Variable "a"))),
      test_node (AndSeparately(
        test_node (True), 
        test_node (AndSeparately (
          test_node (Exists ("b", test_node (Allocation ( "a", test_node (Variable "b"))))),
          test_node (Or(
            test_node (Comparison( Equals, test_node (Variable "x"), test_node (Variable "a"))), 
            test_node (NonAllocated "x")
            ))
        ))
      ))
    ))
  ))
;;

let%test_unit "test formulae n. 13" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected