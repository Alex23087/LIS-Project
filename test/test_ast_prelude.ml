open Failure_ssil_analyzer.Prelude.Analysis
open Failure_ssil_analyzer.Prelude.Analysis.Parser

let annotate_formula node =
  let annotation = LogicFormulas.make_annotation 0 1 in
  AnnotatedNode.make node annotation

let annotate_command node formula =
  let annotation = Commands.make_annotation 0 1 formula in
  AnnotatedNode.make node annotation

let () =
  let formula =
    annotate_formula (LogicFormulas.Formula.NonAllocated("x"))
  in
  let free_x =
    annotate_command (Commands.HeapRegularCommand.Command(
      annotate_command (Commands.HeapAtomicCommand.Free "x") (Option.Some(formula))
    )) Option.None
  in
  let assing_y =
    annotate_command (Commands.HeapRegularCommand.Command(
      annotate_command (Commands.HeapAtomicCommand.Assignment("x",
        annotate_command (Commands.ArithmeticExpression.Literal(50)) Option.None
      )) Option.None
    )) Option.None
  in
  let test_ast = annotate_command (Commands.HeapRegularCommand.Sequence(free_x, assing_y)) Option.None in
  print_endline (Commands.show test_ast)