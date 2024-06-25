(** This module contains the concrete implementation of the Control Flow Graph data structures,
with the definition of the structures contained inside each block.

Important definitions:
- {{! NormalForm.t}Normal Form} - Logic formulas represented in Existential Disjunctive Normal Form.
- {{! Commands.t}Command} - Regular Commands with the updated annotation that contains formulas in normal form.
- {{! Cfg.t}CFG} - Control Flow Graph, instanced on the blocks' record.
- {{! CfgBlock.t}CFG Block} - CFG block record to represent sequences of atomic commands in source.
- {{! Cfg.item}CFG Item} - Control Flow Graph's node, which represent a block of commands, with their predecessor and successor blocks.
*)

include NormalizedFormulas
include CfgCommands

(** The data structure used in the CFG blocks and its functions.

The CFG used in the analysis defines a specific data structure for each block, composed of:
- A visit counter, used to limit the analysis depth.
- A list of atomic commands which compose the block. They are thought as they are separated by sequencing.
Each atomic command contains a post-condition in its annotation.
- A pre-condition on the whole block.
*)
module CfgBlock = struct
  (** Control Flow Graph nodes' content. *)
  type t = {
    visit_count: int;
    precondition: NormalForm.t option;
    statements: Commands.t list;
  }
  [@@deriving show]

  (** Update a block's precondition *)
  let update_precondition (block: t) (formula: NormalForm.t option) = 
    {
      visit_count = block.visit_count;
      precondition = formula;
      statements = block.statements
    }

  (** Update a block's statements list *)
  let update_statements (block: t) (statements: Commands.t list) =
    {
      visit_count = block.visit_count;
      precondition = block.precondition;
      statements = statements
    }

  (** Increase a block's visit count *)
  let increase_visit_count (block: t) = 
    {
      visit_count = block.visit_count + 1;
      precondition = block.precondition;
      statements = block.statements
    }

  (** Update a block's formula given the index of the formula to update.
  
  The zeroeth formula is the pre-condition of the block, while post-conditions start at index 1, one for each command in the list.
  *)
  let update_formula_at (block: t) (update_idx: int) (formula: NormalForm.t option) =
    if update_idx = 0 then
      update_precondition block formula
    else (
      let map_fun idx (statement: Commands.t) = 
        if (idx + 1) = update_idx then
          Commands.update_postcondition statement formula
        else
          statement
      in
      let statements = List.mapi map_fun block.statements in
      update_statements block statements
    )

  (** Update a block's last post-condition, i.e. the start point of the block's analysis. *)
  let update_formula_at_last (block: t) (formula: NormalForm.t option) =
    match List.rev block.statements with
    | [] ->
      update_precondition block formula
    | statement::tail ->
      let statement = Commands.update_postcondition statement formula in
      let statements = List.rev (statement :: tail) in
      update_statements block statements
end

(** Control Flow Graph concrete implementation *)
module Cfg = struct
  include Cfg.CFG

  (** Control Flow Graph. *)
  type t = CfgBlock.t Cfg.CFG.t

  (** Control Flow Graphs' node item. *)
  type item = CfgBlock.t Cfg.CFG.item
end