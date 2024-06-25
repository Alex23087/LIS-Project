open ControlFlowGraph

type analysis_trace = {
  precondition: NormalForm.t;
  trace: Commands.t list;
}
[@@deriving show]

(** Data structure which represent a given state of the analysis *)
type analysis_state = {
  cfg: Cfg.t; [@opaque]
  last_block: int;
  last_statement: int;
  trace: analysis_trace;
}
[@@deriving show]

let get_last_block_precondition (state: analysis_state) =
  let last_block = Cfg.get_data state.cfg state.last_block in
  last_block.precondition

let new_analysis_trace (precondition: NormalForm.t) = 
  {
    precondition;
    trace = [];
  }

let update_trace (trace: analysis_trace) (command: Commands.t) (precondition: NormalForm.t) =
  let old_precondition = trace.precondition in
  let updated_command = Commands.update_postcondition command (Some(old_precondition)) in
  {
    precondition;
    trace = updated_command :: trace.trace;
  }