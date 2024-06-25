open Failure_ssil_analyzer.Ast
open AnnotationLogic

let counter = ref 0

type t = int AnnotationLogic.t
[@@deriving show]

(* Annotate a node with a unique integer *)
let annotate node =
  let out = AnnotatedNode.make node !counter in
  counter := !counter + 1;
  out

let () =
  (* Create an AST corresponding to:  (((x<5) and (x+1==y%2)) or (exists p.(p<=x or p>=y*2)) * (x -> _ and y -> 12)) *)
  let root =
    annotate (Formula.AndSeparately(
      annotate (Formula.Or(
        annotate (Formula.And(
          annotate (Formula.Comparison(
            BinaryComparison.LessThan,
            annotate (ArithmeticExpression.Variable "x"),
            annotate (ArithmeticExpression.Literal 5)
          )),
          annotate (Formula.Comparison(
            BinaryComparison.Equals,
              annotate (ArithmeticExpression.Operation(
                BinaryOperator.Plus,
                annotate (ArithmeticExpression.Variable "x"),
                annotate (ArithmeticExpression.Literal 1)
          )),
          annotate (ArithmeticExpression.Operation(
            BinaryOperator.Modulo,
            annotate (ArithmeticExpression.Variable "y"),
            annotate (ArithmeticExpression.Literal 2)
          ))
        ))
      )),
      annotate (Formula.Exists(
        "p",
        annotate (Formula.Or(
        annotate (Formula.Comparison(
          BinaryComparison.LessOrEqual,
          annotate (ArithmeticExpression.Variable "p"),
          annotate (ArithmeticExpression.Variable "x")
        )),
          annotate (Formula.Comparison(
            BinaryComparison.GreaterOrEqual,
              annotate (ArithmeticExpression.Variable "p"),
              annotate (ArithmeticExpression.Operation(
                BinaryOperator.Times,
                annotate (ArithmeticExpression.Variable "y"),
                annotate (ArithmeticExpression.Literal 2)
              ))
            ))
          ))
        ))
      )),
      annotate (Formula.And(
        annotate (Formula.Exists(
          "v",
          annotate (Formula.Allocation(
            "x",
            annotate (ArithmeticExpression.Variable "v")
          ))
        )),
        annotate (Formula.Allocation(
          "y",
          annotate (ArithmeticExpression.Literal 12)
        ))
      ))
    )) in
  (* Print it with show_rcmd *)
  print_endline (show root)
