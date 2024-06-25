open DataStructures
open Parser

(** Validate Semantics of a given program, from its AST

A program is correct when two specific atomic commands follow some rules:
- {{! Ast.HeapRegularCommands.HeapAtomicCommand.ReadHeap} ReadHeap}: when reading from the heap, it is not allowed to assign the same variable with its heap contents.
- {{! Ast.HeapRegularCommands.HeapAtomicCommand.WriteHeap} WriteHeap}: when writing on the heap, it is not allowed to assign in a cell *x* an expression whose value depends on *x*.

The rules are only enforced to easen the analysis and do not constitute a strict limitation, as they can be easily circumvented by rewriting the program, without changing its semantics.
*)
let validate_ast (ast: Commands.t) = 
  let rec validate_regular_command (cmd: Commands.t) =
    match cmd.node with
    | Command(cmd) -> validate_atomic_command cmd
    | Sequence(left, right) -> validate_regular_command left && validate_regular_command right
    | NondeterministicChoice(left, right) -> validate_regular_command left && validate_regular_command right
    | Star(cmd) -> validate_regular_command cmd
  and validate_atomic_command (cmd: Commands.atomic_t) =
    match cmd.node with
    | Skip -> true
    | Assignment(_, _) -> true
    | NonDet(_) -> true
    | Guard(_) -> true
    | Allocation(_) -> true
    | Free(_) -> true
    | ReadHeap(var, heap_read) -> not (String.equal var heap_read)
    | WriteHeap(heap, expr) ->
      let expr = Analysis_Utils.command_expression_to_logic_expression expr (fun _ -> ()) in
      not (Analysis_Utils.identifier_in_expr expr heap)
  in
  validate_regular_command ast