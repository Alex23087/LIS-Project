open Analysis.DataStructures
open Parser
open Commands
open Test_utils

let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|
  skip;
  skip;
  skip;
  skip
|}

let expected: Commands.t = 
  annotateCommand (HeapRegularCommand.Sequence (
    annotateCommand (HeapRegularCommand.Sequence (
      annotateCommand (HeapRegularCommand.Sequence (
        annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Skip))),
        annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Skip)))
      )),
      annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Skip)))
    )),
    annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Skip)))
  ))

;;

let%test_unit "test commands n. 07" =
  [%test_eq: Commands.t] (parse_command source) expected