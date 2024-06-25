open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open ArithmeticExpression
open Test_utils

open F_utils

let source = {|<< true >>|}

let expected: LogicFormulas.t = test_node (True)
;;

let%test_unit "test formulae n. 00 - 1" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected


let source = {|<< false >>|}

let expected: LogicFormulas.t = test_node (False)
;;

let%test_unit "test formulae n. 00 - 2" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected


let source = {|<< emp >>|}

let expected: LogicFormulas.t = test_node (EmptyHeap)
;;

let%test_unit "test formulae n. 00 - 3" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected


let source = {|<< x -> 0 >>|}

let expected: LogicFormulas.t = test_node (Allocation("x", test_node (Literal 0)))
;;

let%test_unit "test formulae n. 00 - 4" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected


let source = {|<< x -/> >>|}

let expected: LogicFormulas.t = test_node (NonAllocated("x"))
;;

let%test_unit "test formulae n. 00 - 5" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected