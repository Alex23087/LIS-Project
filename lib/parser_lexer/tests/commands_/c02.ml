open Analysis.DataStructures
open Parser
open Commands
open Test_utils
let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|y = alloc();
[y] = 2 * 300;
if (y == 600) then {
  y = nondet()
} else {
  skip
};
free(y)
|}

let expected: Commands.t =
  annotateCommand (HeapRegularCommand.Sequence ( (*y;[y];if; , free;*)
    annotateCommand (HeapRegularCommand.Sequence ( (*y;[y]; , if*)
      annotateCommand (HeapRegularCommand.Sequence( (*y;[y]*)
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.Allocation "y")
        )),
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.WriteHeap (
            "y",
            annotateCommand (Commands.ArithmeticExpression.BinaryOperation (
              ArithmeticOperation.Times,
              annotateCommand (Commands.ArithmeticExpression.Literal 2),
              annotateCommand (Commands.ArithmeticExpression.Literal 300)
            ))
          ))
        ))
      )), (*if..then..else;*)
      annotateCommand (HeapRegularCommand.NondeterministicChoice (
        annotateCommand (HeapRegularCommand.Sequence (  (*b;then*)
          annotateCommand (HeapRegularCommand.Command (
            annotateCommand (HeapAtomicCommand.Guard(
              annotateCommand (BooleanExpression.Comparison(
                BooleanComparison.Equal,
                annotateCommand (Commands.ArithmeticExpression.Variable "y"),
                annotateCommand (Commands.ArithmeticExpression.Literal 600)
              ))
            ))
          )),
          annotateCommand (HeapRegularCommand.Command(
            annotateCommand (HeapAtomicCommand.NonDet "y")
          ))
        )),
        annotateCommand (HeapRegularCommand.Sequence( (*not b;else*)
          annotateCommand (HeapRegularCommand.Command (
            annotateCommand (HeapAtomicCommand.Guard(
              annotateCommand (BooleanExpression.Not(
                annotateCommand (BooleanExpression.Comparison(
                  BooleanComparison.Equal,
                  annotateCommand (Commands.ArithmeticExpression.Variable "y"),
                  annotateCommand (Commands.ArithmeticExpression.Literal 600)
                ))
              ))
            ))
          )),
          annotateCommand (HeapRegularCommand.Command (
            annotateCommand (HeapAtomicCommand.Skip)
          ))
        ))
      ))
    )),
    annotateCommand (HeapRegularCommand.Command (
        annotateCommand (HeapAtomicCommand.Free "y")
    ))
  ))
;;

let%test_unit "test commands n. 02" =
  [%test_eq: Commands.t] (parse_command source) expected
