open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open Test_utils

open F_utils

let source = {|<< exists x . true >>|}

let expected: LogicFormulas.t =
  test_node (Exists(
    "x", test_node (True)
  ))
;;

let%test_unit "test formulae n. 01" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected