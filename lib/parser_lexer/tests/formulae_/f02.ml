open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open Test_utils

open F_utils

let source = {|<< true && true >>|}

let expected: LogicFormulas.t =
  test_node (And( test_node (True), test_node (True)))
;;

let%test_unit "test formulae n. 02" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected