open Analysis.DataStructures.Parser
open Analysis.DataStructures
open Parsing
let dummy_position = { line = -1; column = -1 }

let rec remove_position_from_annotations (command: Commands.t) =
  let logic_formula = match command.annotation.logic_formula with
    | None -> None
    | Some f -> Some (remove_position_from_annotations_formulae f) in
  let newAnnot = Commands.make_annotation_position dummy_position logic_formula in
  match command.node with
  | Commands.HeapRegularCommand.Star c -> AnnotatedNode.make (Commands.HeapRegularCommand.Star (remove_position_from_annotations c)) newAnnot
  | Commands.HeapRegularCommand.Sequence (c1, c2) -> AnnotatedNode.make (Commands.HeapRegularCommand.Sequence ((remove_position_from_annotations c1), (remove_position_from_annotations c2))) newAnnot
  | Commands.HeapRegularCommand.NondeterministicChoice (c1, c2) -> AnnotatedNode.make (Commands.HeapRegularCommand.NondeterministicChoice ((remove_position_from_annotations c1), (remove_position_from_annotations c2))) newAnnot
  | Commands.HeapRegularCommand.Command c -> AnnotatedNode.make (Commands.HeapRegularCommand.Command (remove_position_from_annotations_atomic c)) newAnnot

and remove_position_from_annotations_atomic (atomic_command: Commands.atomic_t): Commands.atomic_t =
  let logic_formula = match atomic_command.annotation.logic_formula with
    | None -> None
    | Some f -> Some (remove_position_from_annotations_formulae f) in
  let newAnnot = Commands.make_annotation_position dummy_position logic_formula in
  match atomic_command.node with
  | Commands.HeapAtomicCommand.Skip -> AnnotatedNode.make Commands.HeapAtomicCommand.Skip newAnnot
  | Commands.HeapAtomicCommand.Allocation id -> AnnotatedNode.make (Commands.HeapAtomicCommand.Allocation id) newAnnot
  | Commands.HeapAtomicCommand.Free id -> AnnotatedNode.make (Commands.HeapAtomicCommand.Free id) newAnnot
  | Commands.HeapAtomicCommand.Assignment (id, ae) -> AnnotatedNode.make (Commands.HeapAtomicCommand.Assignment (id, remove_position_from_annotations_aexp ae)) newAnnot
  | Commands.HeapAtomicCommand.Guard be -> AnnotatedNode.make (Commands.HeapAtomicCommand.Guard (remove_position_from_annotations_bexp be)) newAnnot
  | Commands.HeapAtomicCommand.NonDet id -> AnnotatedNode.make (Commands.HeapAtomicCommand.NonDet id) newAnnot
  | Commands.HeapAtomicCommand.ReadHeap (id1,id2) -> AnnotatedNode.make (Commands.HeapAtomicCommand.ReadHeap (id1,id2)) newAnnot
  | Commands.HeapAtomicCommand.WriteHeap (id1, ae) -> AnnotatedNode.make (Commands.HeapAtomicCommand.WriteHeap (id1, remove_position_from_annotations_aexp ae)) newAnnot
and remove_position_from_annotations_aexp (aexp: Commands.arithmetic_t): Commands.arithmetic_t =
  let logic_formula = match aexp.annotation.logic_formula with
    | None -> None
    | Some f -> Some (remove_position_from_annotations_formulae f) in
  let newAnnot = Commands.make_annotation_position dummy_position logic_formula in
  match aexp.node with
  | Commands.ArithmeticExpression.Variable id -> AnnotatedNode.make (Commands.ArithmeticExpression.Variable id) newAnnot
  | Commands.ArithmeticExpression.Literal i -> AnnotatedNode.make (Commands.ArithmeticExpression.Literal i) newAnnot
  | Commands.ArithmeticExpression.BinaryOperation (aop, ae1, ae2) -> AnnotatedNode.make (Commands.ArithmeticExpression.BinaryOperation (aop, (remove_position_from_annotations_aexp ae1), (remove_position_from_annotations_aexp ae2))) newAnnot

and remove_position_from_annotations_bexp (bexp: Commands.boolean_t): Commands.boolean_t =
  let logic_formula = match bexp.annotation.logic_formula with
    | None -> None
    | Some f -> Some (remove_position_from_annotations_formulae f) in
  let newAnnot = Commands.make_annotation_position dummy_position logic_formula in
  match bexp.node with
  | Commands.BooleanExpression.True -> AnnotatedNode.make Commands.BooleanExpression.True newAnnot
  | Commands.BooleanExpression.False -> AnnotatedNode.make Commands.BooleanExpression.False newAnnot
  | Commands.BooleanExpression.Not be -> AnnotatedNode.make (Commands.BooleanExpression.Not (remove_position_from_annotations_bexp be)) newAnnot
  | Commands.BooleanExpression.And (be1, be2) -> AnnotatedNode.make (Commands.BooleanExpression.And ((remove_position_from_annotations_bexp be1), (remove_position_from_annotations_bexp be2))) newAnnot
  | Commands.BooleanExpression.Or (be1, be2) -> AnnotatedNode.make (Commands.BooleanExpression.Or ((remove_position_from_annotations_bexp be1), (remove_position_from_annotations_bexp be2))) newAnnot
  | Commands.BooleanExpression.Comparison (bc, ae1, ae2) -> AnnotatedNode.make (Commands.BooleanExpression.Comparison (bc, (remove_position_from_annotations_aexp ae1), (remove_position_from_annotations_aexp ae2))) newAnnot
and remove_position_from_annotations_formulae (formula: LogicFormulas.t): LogicFormulas.t =
  let newAnnot = LogicFormulas.make_annotation_position dummy_position in
  match formula.node with
  | LogicFormulas.Formula.True -> AnnotatedNode.make LogicFormulas.Formula.True newAnnot
  | LogicFormulas.Formula.False -> AnnotatedNode.make LogicFormulas.Formula.False newAnnot
  | LogicFormulas.Formula.EmptyHeap -> AnnotatedNode.make LogicFormulas.Formula.EmptyHeap newAnnot
  | LogicFormulas.Formula.NonAllocated id -> AnnotatedNode.make (LogicFormulas.Formula.NonAllocated id) newAnnot
  | LogicFormulas.Formula.Or (f1, f2) -> AnnotatedNode.make (LogicFormulas.Formula.Or ((remove_position_from_annotations_formulae f1), (remove_position_from_annotations_formulae f2))) newAnnot
  | LogicFormulas.Formula.And (f1, f2) -> AnnotatedNode.make (LogicFormulas.Formula.And ((remove_position_from_annotations_formulae f1), (remove_position_from_annotations_formulae f2))) newAnnot
  | LogicFormulas.Formula.Exists (id, f) -> AnnotatedNode.make (LogicFormulas.Formula.Exists (id, (remove_position_from_annotations_formulae f))) newAnnot
  | LogicFormulas.Formula.AndSeparately (f1, f2) -> AnnotatedNode.make (LogicFormulas.Formula.AndSeparately ((remove_position_from_annotations_formulae f1), (remove_position_from_annotations_formulae f2))) newAnnot
  | LogicFormulas.Formula.Comparison (bc, ae1, ae2) -> AnnotatedNode.make (LogicFormulas.Formula.Comparison (bc, (remove_position_from_annotations_formulae_aexp ae1), (remove_position_from_annotations_formulae_aexp ae2))) newAnnot
  | LogicFormulas.Formula.Allocation (id, ae) -> AnnotatedNode.make (LogicFormulas.Formula.Allocation (id, (remove_position_from_annotations_formulae_aexp ae))) newAnnot

and remove_position_from_annotations_formulae_aexp (aexp: LogicFormulas.arithmetic_t): LogicFormulas.arithmetic_t =
  let newAnnot = LogicFormulas.make_annotation_position dummy_position in
  match aexp.node with
  | LogicFormulas.ArithmeticExpression.Variable id -> AnnotatedNode.make (LogicFormulas.ArithmeticExpression.Variable id) newAnnot
  | LogicFormulas.ArithmeticExpression.Literal i -> AnnotatedNode.make (LogicFormulas.ArithmeticExpression.Literal i) newAnnot
  | LogicFormulas.ArithmeticExpression.Operation (op, ae1, ae2) -> AnnotatedNode.make (LogicFormulas.ArithmeticExpression.Operation (op, (remove_position_from_annotations_formulae_aexp ae1), (remove_position_from_annotations_formulae_aexp ae2))) newAnnot


let parse_command source = let lexbuf = Lexing.from_string ~with_positions:true source in
              let ast = parse Lexer.lex lexbuf in
                match Either.find_left ast with
                | Some command -> remove_position_from_annotations command
                | None -> raise (Failure "not a command");;

let parse_formula source = let lexbuf = Lexing.from_string ~with_positions:true source in
              let ast = parse Lexer.lex lexbuf in
                match Either.find_right ast with
                | Some formula -> remove_position_from_annotations_formulae formula
                | None -> raise (Failure "not a formula");;