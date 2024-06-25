open Analysis.DataStructures
open Parser
open Commands
open LogicFormulas
open Test_utils
let emptyAnnotation = {position = dummy_position; logic_formula = None}
let annotateCommand formula =
  AnnotatedNode.make formula emptyAnnotation

(* annotation goes on if *)
let source = {|
  if (x < -(1 + 3))
    then x = (x*(-1))-4
    else skip
  << x -> 1 >>
|}

let expected: Commands.t = { node =
  (HeapRegularCommand.NondeterministicChoice (
     { node =
       (HeapRegularCommand.Sequence (
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Guard
                    { node =
                      (BooleanExpression.Comparison (
                         BooleanComparison.LessThan,
                         { node =
                           (Commands.ArithmeticExpression.Variable
                              "x");
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           },
                         { node =
                           (Commands.ArithmeticExpression.BinaryOperation (
                              ArithmeticOperation.Minus,
                              { node =
                                (Commands.ArithmeticExpression.Literal
                                   0);
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                },
                              { node =
                                (Commands.ArithmeticExpression.BinaryOperation (
                                   ArithmeticOperation.Plus,
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        1);
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     },
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        3);
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     }
                                   ));
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           }
                         ));
                      annotation =
                      { position =
                        dummy_position;
                        logic_formula = None }
                      });
                 annotation =
                 { position =
                   dummy_position; logic_formula = None
                   }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            },
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Assignment (
                    "x",
                    { node =
                      (Commands.ArithmeticExpression.BinaryOperation (
                         ArithmeticOperation.Minus,
                         { node =
                           (Commands.ArithmeticExpression.BinaryOperation (
                              ArithmeticOperation.Times,
                              { node =
                                (Commands.ArithmeticExpression.Variable
                                   "x");
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                },
                              { node =
                                (Commands.ArithmeticExpression.Literal (-1));
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           },
                         { node =
                           (Commands.ArithmeticExpression.Literal
                              4);
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           }
                         ));
                      annotation =
                      { position =
                        dummy_position;
                        logic_formula = None }
                      }
                    ));
                 annotation =
                 { position =
                   dummy_position;
                   logic_formula = None }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            }
          ));
       annotation =
       { position = dummy_position;
         logic_formula = None }
       },
     { node =
       (HeapRegularCommand.Sequence (
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Guard
                    { node =
                      (BooleanExpression.Not
                         { node =
                           (BooleanExpression.Comparison (
                              BooleanComparison.LessThan,
                              { node =
                                (Commands.ArithmeticExpression.Variable
                                   "x");
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                },
                              { node =
                                (Commands.ArithmeticExpression.BinaryOperation (
                                   ArithmeticOperation.Minus,
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        0);
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     },
                                   { node =
                                     (Commands.ArithmeticExpression.BinaryOperation (
                                        ArithmeticOperation.Plus,
                                        { node =
                                          (Commands.ArithmeticExpression.Literal
                                             1);
                                          annotation =
                                          { position =
                                           dummy_position;
                                            logic_formula = None }
                                          },
                                        { node =
                                          (Commands.ArithmeticExpression.Literal
                                             3);
                                          annotation =
                                          { position =
                                            dummy_position;
                                            logic_formula = None }
                                          }
                                        ));
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     }
                                   ));
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           });
                      annotation =
                      { position =
                        dummy_position;
                        logic_formula = None }
                      });
                 annotation =
                 { position =
                   dummy_position; logic_formula = None
                   }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            },
          { node =
            (HeapRegularCommand.Command
               { node =
                 HeapAtomicCommand.Skip;
                 annotation =
                 { position =
                   dummy_position;
                   logic_formula = None }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            }
          ));
       annotation =
       { position = dummy_position;
         logic_formula = None }
       }
     ));
  annotation =
  { position = dummy_position;
    logic_formula =
    (Some { node =
            (Formula.Allocation ("x",
               { node =
                 (ArithmeticExpression.Literal
                    1);
                 annotation =
                 { position =
                   dummy_position}
                 }
               ));
            annotation =
            { position = dummy_position}
            })
    }
  }

let%test_unit "test commands n. 08 - 01" =
  [%test_eq: Commands.t] (parse_command source) expected


(* annotation goes on skip *)
let source_2 = {|
  if (x < -(1 + 3))
    then x = (x*(-1))-4
    else { skip << x -> 1 >> }
|}

let expected_2: Commands.t = { node =
  (HeapRegularCommand.NondeterministicChoice (
     { node =
       (HeapRegularCommand.Sequence (
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Guard
                    { node =
                      (BooleanExpression.Comparison (
                         BooleanComparison.LessThan,
                         { node =
                           (Commands.ArithmeticExpression.Variable
                              "x");
                           annotation =
                           { position =
                             dummy_position;                             logic_formula = None }
                           },
                         { node =
                           (Commands.ArithmeticExpression.BinaryOperation (
                              ArithmeticOperation.Minus,
                              { node =
                                (Commands.ArithmeticExpression.Literal
                                   0);
                                annotation =
                                { position =
                                  dummy_position;                                  logic_formula = None }
                                },
                              { node =
                                (Commands.ArithmeticExpression.BinaryOperation (
                                   ArithmeticOperation.Plus,
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        1);
                                     annotation =
                                     { position =
                                       dummy_position;                                       logic_formula = None }
                                     },
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        3);
                                     annotation =
                                     { position =
                                       dummy_position;                                       logic_formula = None }
                                     }
                                   ));
                                annotation =
                                { position =
                                  dummy_position;                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;                             logic_formula = None }
                           }
                         ));
                      annotation =
                      { position =
                        dummy_position;                        logic_formula = None }
                      });
                 annotation =
                 { position =
                   dummy_position; logic_formula = None
                   }
                 });
            annotation =
            { position = dummy_position;              logic_formula = None }
            },
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Assignment (
                    "x",
                    { node =
                      (Commands.ArithmeticExpression.BinaryOperation (
                         ArithmeticOperation.Minus,
                         { node =
                           (Commands.ArithmeticExpression.BinaryOperation (
                              ArithmeticOperation.Times,
                              { node =
                                (Commands.ArithmeticExpression.Variable
                                   "x");
                                annotation =
                                { position =
                                  dummy_position;                                  logic_formula = None }
                                },
                              { node = (Commands.ArithmeticExpression.Literal (-1));
                                annotation =
                                { position =
                                  dummy_position;                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;                             logic_formula = None }
                           },
                         { node =
                           (Commands.ArithmeticExpression.Literal
                              4);
                           annotation =
                           { position =
                             dummy_position;                             logic_formula = None }
                           }
                         ));
                      annotation =
                      { position =
                        dummy_position;                        logic_formula = None }
                      }
                    ));
                 annotation =
                 { position =
                   dummy_position;
                   logic_formula = None }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            }
          ));
       annotation =
       { position = dummy_position;
         logic_formula = None }
       },
     { node =
       (HeapRegularCommand.Sequence (
          { node =
            (HeapRegularCommand.Command
               { node =
                 (HeapAtomicCommand.Guard
                    { node =
                      (BooleanExpression.Not
                         { node =
                           (BooleanExpression.Comparison (
                              BooleanComparison.LessThan,
                              { node =
                                (Commands.ArithmeticExpression.Variable
                                   "x");
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                },
                              { node =
                                (Commands.ArithmeticExpression.BinaryOperation (
                                   ArithmeticOperation.Minus,
                                   { node =
                                     (Commands.ArithmeticExpression.Literal
                                        0);
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     },
                                   { node =
                                     (Commands.ArithmeticExpression.BinaryOperation (
                                        ArithmeticOperation.Plus,
                                        { node =
                                          (Commands.ArithmeticExpression.Literal
                                             1);
                                          annotation =
                                          { position = dummy_position;
                                            logic_formula = None }
                                          },
                                        { node =
                                          (Commands.ArithmeticExpression.Literal
                                             3);
                                          annotation =
                                          { position = dummy_position;
                                            logic_formula = None }
                                          }
                                        ));
                                     annotation =
                                     { position =
                                       dummy_position;
                                       logic_formula = None }
                                     }
                                   ));
                                annotation =
                                { position =
                                  dummy_position;
                                  logic_formula = None }
                                }
                              ));
                           annotation =
                           { position =
                             dummy_position;
                             logic_formula = None }
                           });
                      annotation =
                      { position =
                        dummy_position;
                        logic_formula = None }
                      });
                 annotation =
                 { position =
                   dummy_position; logic_formula = None
                   }
                 });
            annotation =
            { position = dummy_position;
              logic_formula = None }
            },
          { node =
            (HeapRegularCommand.Command
               { node =
                 HeapAtomicCommand.Skip;
                 annotation =
                 { position =
                   dummy_position;
                   logic_formula = None }
                 });
            annotation =
            { position = dummy_position;
              logic_formula =
              (Some { node =
                      (LogicFormulas.Formula.Allocation (
                         "x",
                         { node =
                           (ArithmeticExpression.Literal
                              1);
                           annotation =
                           { position =
                             dummy_position }
                           }
                         ));
                      annotation =
                      { position =
                        dummy_position }
                      })
              }
            }
          ));
       annotation =
       { position = dummy_position;         logic_formula = None }
       }
     ));
  annotation =
  { position = dummy_position;    logic_formula = None }
  }

let%test_unit "test commands n. 08 - 02" =
  [%test_eq: Commands.t] (parse_command source_2) expected_2