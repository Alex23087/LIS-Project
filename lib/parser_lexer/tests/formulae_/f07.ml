open Analysis.DataStructures
open Parser
open LogicFormulas
open Formula
open Test_utils

open F_utils

let source = {|<< x -/> || emp >>|}

let expected: LogicFormulas.t =
  test_node (Or (
    test_node (NonAllocated "x"),
    test_node (EmptyHeap)
  ))
;;

let%test_unit "test formulae n. 07" =
  [%test_eq: LogicFormulas.t] (parse_formula source) expected