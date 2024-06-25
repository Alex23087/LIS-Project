open Analysis.DataStructures
open Parser
open LogicFormulas
open Test_utils

let test_node (formula) = AnnotatedNode.make formula { position = dummy_position }