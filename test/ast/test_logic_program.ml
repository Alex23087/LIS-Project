open Lisproject.Ast
open Sexplib.Std
open Ppx_compare_lib.Builtin

(* Instantiate the AST with the annotation type *)
module ASTLogic = AnnotationLogic(struct
  type t = int (* int annotations *) [@@deriving show, sexp, compare]
end)

open ASTLogic

let counter = ref 0

(* Annotate a node with a unique integer *)
let annotate (node: 'a): 'a AnnotatedNode.t =
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
