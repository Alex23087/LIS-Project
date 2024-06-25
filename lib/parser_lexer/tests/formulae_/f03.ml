open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open Test_utils

open F_utils

let source = {|<< true || false >>|}

let expected: LogicFormulas.t =
  test_node (Or( test_node (True), test_node (False)))
;;

let%test_unit "test formulae n. 03" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected