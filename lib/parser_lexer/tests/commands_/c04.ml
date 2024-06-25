open Analysis.DataStructures
open Parser
open Commands
open Test_utils

let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|x = alloc();
y = alloc();
if (x == y || x != y && true) then {
  [x] = 42;
  free(x)
} else {
  [y] = 0;
  free(y)
};
skip
|}

let expected: Commands.t =
  annotateCommand (HeapRegularCommand.Sequence (
    annotateCommand (HeapRegularCommand.Sequence (
      annotateCommand (HeapRegularCommand.Sequence (
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.Allocation "x")
        )),
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.Allocation "y")
        ))
      )),
      annotateCommand (HeapRegularCommand.NondeterministicChoice(
        annotateCommand (HeapRegularCommand.Sequence(
          annotateCommand (HeapRegularCommand.Command ( annotateCommand (HeapAtomicCommand.Guard(
            annotateCommand (BooleanExpression.Or (
              annotateCommand (BooleanExpression.Comparison (
                BooleanComparison.Equal,
                annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                annotateCommand (Commands.ArithmeticExpression.Variable "y")
              )),
              annotateCommand (BooleanExpression.And (
                annotateCommand (BooleanExpression.Comparison (
                  BooleanComparison.NotEqual,
                  annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                  annotateCommand (Commands.ArithmeticExpression.Variable "y")
                )),
                annotateCommand (BooleanExpression.True)
              ))
            ))
          )))), (*body*)
          annotateCommand (HeapRegularCommand.Sequence (
            annotateCommand (HeapRegularCommand.Command (
              annotateCommand (HeapAtomicCommand.WriteHeap (
                "x",
                annotateCommand (Commands.ArithmeticExpression.Literal 42)
              ))
            )),
            annotateCommand (HeapRegularCommand.Command (
              annotateCommand (HeapAtomicCommand.Free "x")
            ))
          ))
        )), (*not b?;else*)
        annotateCommand (HeapRegularCommand.Sequence(
          annotateCommand (HeapRegularCommand.Command ( annotateCommand (HeapAtomicCommand.Guard(
            annotateCommand (BooleanExpression.Not(
              annotateCommand (BooleanExpression.Or (
                annotateCommand (BooleanExpression.Comparison (
                  BooleanComparison.Equal,
                  annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                  annotateCommand (Commands.ArithmeticExpression.Variable "y")
                )),
                annotateCommand (BooleanExpression.And (
                  annotateCommand (BooleanExpression.Comparison (
                    BooleanComparison.NotEqual,
                    annotateCommand (Commands.ArithmeticExpression.Variable "x"),
                    annotateCommand (Commands.ArithmeticExpression.Variable "y")
                  )),
                  annotateCommand (BooleanExpression.True)
                ))
              ))
            ))
          )))),
          annotateCommand (HeapRegularCommand.Sequence( (*else body*)
            annotateCommand (HeapRegularCommand.Command (
              annotateCommand (HeapAtomicCommand.WriteHeap (
                "y",
                annotateCommand (Commands.ArithmeticExpression.Literal 0)
              ))
            )),
            annotateCommand (HeapRegularCommand.Command (
              annotateCommand (HeapAtomicCommand.Free "y")
            ))
          ))
        ))
      ))
    )),
    annotateCommand (HeapRegularCommand.Command (
        annotateCommand HeapAtomicCommand.Skip
    ))
  ))
;;

let%test_unit "test commands n. 04" =
  [%test_eq: Commands.t] (parse_command source) expected
