open Analysis.DataStructures
open Parser
open Commands
open Test_utils
let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|
  x = alloc();
  while (x < 10) {
    x = x + 1
  }
|}

let expected: Commands.t =
  annotateCommand (HeapRegularCommand.Sequence (
    annotateCommand(HeapRegularCommand.Command (
      annotateCommand(HeapAtomicCommand.Allocation "x")
    )),
    annotateCommand(HeapRegularCommand.Sequence(
      annotateCommand (HeapRegularCommand.Star (
        annotateCommand (HeapRegularCommand.Sequence(
          annotateCommand (HeapRegularCommand.Command (
            annotateCommand (HeapAtomicCommand.Guard (
              annotateCommand (BooleanExpression.Comparison (
                BooleanComparison.LessThan,
                annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                annotateCommand (Commands.ArithmeticExpression.Literal 10)
              ))
            ))
          )),
          annotateCommand (HeapRegularCommand.Command (
            annotateCommand (HeapAtomicCommand.Assignment (
              "x",
              annotateCommand (Commands.ArithmeticExpression.BinaryOperation (
                ArithmeticOperation.Plus,
                annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                annotateCommand (Commands.ArithmeticExpression.Literal 1)
              ))
            ))
          ))
        ))
      )),
      annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Guard (
          annotateCommand (BooleanExpression.Not (
            annotateCommand (BooleanExpression.Comparison (
              BooleanComparison.LessThan,
              annotateCommand (Commands.ArithmeticExpression.Variable "x"),
              annotateCommand (Commands.ArithmeticExpression.Literal 10)
            ))
          ))
        ))
      ))
    ))
  ))
;;

let%test_unit "test commands n. 06" =
  [%test_eq: Commands.t] (parse_command source) expected
