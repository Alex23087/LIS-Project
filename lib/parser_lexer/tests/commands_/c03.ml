open Analysis.DataStructures
open Parser
open Commands
open Test_utils
let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

let source = {|z = alloc();
[z] = 5 * (10 + 2);
while (z != 0) {
  z = z - 1
};
free(z)
|}

let expected: Commands.t =

  annotateCommand (HeapRegularCommand.Sequence(
    annotateCommand (HeapRegularCommand.Sequence (
      annotateCommand (HeapRegularCommand.Sequence (
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.Allocation "z")
        )),
        annotateCommand (HeapRegularCommand.Command (
          annotateCommand (HeapAtomicCommand.WriteHeap (
            "z",
            annotateCommand (Commands.ArithmeticExpression.BinaryOperation (
              ArithmeticOperation.Times,
              annotateCommand (Commands.ArithmeticExpression.Literal 5),
              annotateCommand (Commands.ArithmeticExpression.BinaryOperation (
                ArithmeticOperation.Plus,
                annotateCommand (Commands.ArithmeticExpression.Literal 10),
                annotateCommand (Commands.ArithmeticExpression.Literal 2)
              ))
            ))
          ))
        ))
      )),
      annotateCommand (HeapRegularCommand.Sequence (
        annotateCommand (HeapRegularCommand.Star (
          annotateCommand (HeapRegularCommand.Sequence (
            annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Guard(
              annotateCommand (BooleanExpression.Comparison(
                BooleanComparison.NotEqual,
                annotateCommand (Commands.ArithmeticExpression.Variable "z"),
                annotateCommand (Commands.ArithmeticExpression.Literal 0)
              ))
            )))),
            annotateCommand (HeapRegularCommand.Command(
              annotateCommand (HeapAtomicCommand.Assignment(
                "z",
                annotateCommand (Commands.ArithmeticExpression.BinaryOperation (
                  ArithmeticOperation.Minus,
                  annotateCommand (Commands.ArithmeticExpression.Variable "z"),
                  annotateCommand (Commands.ArithmeticExpression.Literal 1)
                ))
              ))
            ))
          ))
        )),
        annotateCommand (HeapRegularCommand.Command (annotateCommand (HeapAtomicCommand.Guard(
          annotateCommand (BooleanExpression.Not(
            annotateCommand (BooleanExpression.Comparison(
              BooleanComparison.NotEqual,
              annotateCommand (Commands.ArithmeticExpression.Variable "z"),
              annotateCommand (Commands.ArithmeticExpression.Literal 0)
            ))
          ))
        ))))
      ))
    )),
    annotateCommand (HeapRegularCommand.Command( annotateCommand (HeapAtomicCommand.Free "z") ))

  ));;

let%test_unit "test commands n. 03" =
  [%test_eq: Commands.t] (parse_command source) expected
