open Lisproject.Prelude.Ast.Commands
open Lisproject.Prelude.Ast.LogicFormulas
open Lisproject.Prelude.Ast.Commands.AnnotatedNode
open Lisproject.Prelude.Ast.LogicFormulas.AnnotatedNode
open Lisproject.Parserlexer

let source_00 = {|x = alloc();
[x] = 1 + 400 << (exists y . x -> y) * emp >>;
free(x) << x -/> * emp >>
|}

let expected_00: HeapRegularCommand.t = {
  node = (HeapRegularCommand.Sequence (
    {
      node = (HeapRegularCommand.Sequence (
        {
          node = (HeapRegularCommand.Command {
            node = (HeapAtomicCommand.Allocation "x");
            annotation = {
              position = { line = 1; column = 0 };
              logic_formula = None
            }
          });
          annotation = {
            position = { line = 1; column = 0 };
            logic_formula = None
          }
        },
        {
          node = (HeapRegularCommand.Command {
            node = (HeapAtomicCommand.WriteHeap (
              "x",
              {
                node = (BinaryOperation (
                  ArithmeticOperation.Plus,
                  {
                    node = (Literal 1);
                    annotation = {
                      position = { line = 2; column = 19 };
                      logic_formula = None
                    }
                  },
                  {
                    node = (Literal 400);
                    annotation = {
                      position = { line = 2; column = 23 };
                      logic_formula = None
                    }
                  }
                ));
                annotation = {
                  position = { line = 2; column = 19 };
                  logic_formula = None
                }
              }
            ));
            annotation = {
              position = { line = 2; column = 13 };
              logic_formula = None
            }
          });
          annotation = {
            position = { line = 2; column = 13 };
            logic_formula = (Some {
              node = (Formula.AndSeparately (
                {
                  node = (Formula.Exists (
                    "y",
                    {
                      node = (Formula.Allocation (
                        "x",
                        {
                          node = (Variable "y");
                          annotation = {
                            position = { line = 2; column = 47 }
                          }
                        }
                      ));
                      annotation = {
                        position = { line = 2; column = 42 }
                      }
                    }
                  ));
                  annotation = {
                    position = { line = 2; column = 31 }
                  }
                },
                {
                  node = Formula.EmptyHeap;
                  annotation = {
                    position = { line = 2; column = 52 }
                  }
                }
              ));
              annotation = {
                position = { line = 2; column = 30 }
              }
            })
          }
        }
      ));
      annotation = {
        position = { line = 1; column = 0 };
        logic_formula = None
      }
    },
    {
      node = (HeapRegularCommand.Command {
        node = (HeapAtomicCommand.Free "x");
        annotation = {
          position = { line = 3; column = 60 };
          logic_formula = None
        }
      });
      annotation = {
        position = { line = 3; column = 60 };
        logic_formula = (Some {
          node = (Formula.AndSeparately (
            {
              node = (Formula.NonAllocated "x");
              annotation = {
                position = { line = 3; column = 71 }
              }
            },
            {
              node = Formula.EmptyHeap;
              annotation = {
                position = { line = 3; column = 79 }
              }
            }
          ));
          annotation = {
            position = { line = 3; column = 71 }
          }
        })
      }
    }
  ));
  annotation = {
    position = { line = 1; column = 0 };
    logic_formula = None
  }
}
;;

let test_00 = let lexbuf = Lexing.from_string ~with_positions:true source_00 in
              let ast = Parsing.parse Lexer.lex lexbuf in
                match Either.find_left ast with
                | Some command -> let res = (command = expected_00) in
                    if res then () else raise (Failure "test_00")
                | None -> raise (Failure "test_00 is not a command");;

let () = test_00;;