open Analysis.DataStructures
open Parser
open Commands
open Test_utils

let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|
  if (x == 0) then {
    x = 1
  } else {
    skip
  }
|}

let expected: Commands.t = 
  annotateCommand (HeapRegularCommand.NondeterministicChoice (
    annotateCommand (HeapRegularCommand.Sequence (
      annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Guard (
          annotateCommand (BooleanExpression.Comparison (
            BooleanComparison.Equal,
            annotateCommand (Commands.ArithmeticExpression.Variable "x"),
            annotateCommand (Commands.ArithmeticExpression.Literal 0)
          ))
        ))
      )),
      annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Assignment (
          "x",
          annotateCommand (Commands.ArithmeticExpression.Literal 1)
        ))
      ))
    )),
    annotateCommand (HeapRegularCommand.Sequence (
      annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Guard (
          annotateCommand (BooleanExpression.Not(
            annotateCommand (BooleanExpression.Comparison (
              BooleanComparison.Equal,
              annotateCommand (Commands.ArithmeticExpression.Variable "x"),
              annotateCommand (Commands.ArithmeticExpression.Literal 0)
            ))
          ))
          
        ))
      )),
      annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Skip)
      ))
    ))
  ))

;;

let%test_unit "test commands n. 05" =
  [%test_eq: Commands.t] (parse_command source) expected
