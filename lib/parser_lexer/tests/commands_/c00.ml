open Analysis.DataStructures.Parser
open Test_utils

let source = {|skip|}

let expected: Commands.t = {
  node = Commands.HeapRegularCommand.Command {
    node = Commands.HeapAtomicCommand.Skip;
    annotation = {position = dummy_position; logic_formula = None}
  };
  annotation = {position = dummy_position; logic_formula = None}
}
;;

let%test_unit "test commands n. 00" =
  [%test_eq: Commands.t] (parse_command source) expected