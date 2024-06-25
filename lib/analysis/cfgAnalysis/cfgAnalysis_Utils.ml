open DataStructures.Analysis
open Utils
let get_postcondition = Commands.get_postcondition
let update_postcondition = Commands.update_postcondition

let starting_states (cfg: Cfg.t) =
  let block_start_postconditions (block: CfgBlock.t) =
    let fold_fun (start_data, command_index) statement =
      match get_postcondition statement with
      | Some(formula) -> (command_index, formula) :: start_data, command_index + 1
      | None -> start_data, command_index + 1
    in
    let start_data =
      match block.precondition with
      | Some(formula) -> [ 0, formula ]
      | None -> []
    in
    let start_data, _ = List.fold_left fold_fun (start_data, 1) block.statements in
    start_data
  in
  let starting_states (cfg: Cfg.t) (item: Cfg.item) =
    let idx = Cfg.get_id item in
    let block = Cfg.get_data cfg idx in
    let map_fun (statement_idx, postcondition) = 
      {cfg; last_block = idx; last_statement = statement_idx; trace = new_analysis_trace postcondition}
    in
    let start_postconditions = block_start_postconditions block in
    List.map map_fun start_postconditions
  in
  Cfg.fold cfg (fun cfg x acc -> (starting_states cfg x) @ acc) []

let visit_limit (block: CfgBlock.t) =
  block.visit_count >= 10

let block_analysis_step (block: CfgBlock.t) (last_statement: int) : CfgBlock.t =
  let statement = unwrap_option (List.nth_opt block.statements (last_statement - 1)) "unexpected" in
  let postcondition = unwrap_option (get_postcondition statement) "unexpected" in
  let precondition = Some(Atomic.compute_precondition statement postcondition) in
  CfgBlock.update_formula_at block (last_statement - 1) precondition

let analysis_step (state: analysis_state) : analysis_state list * analysis_state list =
  let block_to_starting_state (cfg: Cfg.t) (last_block: int) (block: CfgBlock.t) =
    let cfg = Cfg.set_data cfg last_block block in
    {
      cfg = cfg;
      last_block = last_block;
      last_statement = List.length block.statements;
      trace = state.trace
    }
  in
  let block_analysis_state (cfg: Cfg.t) (last_block: int) (last_statement: int) (block: CfgBlock.t) =
    let cfg = Cfg.set_data cfg last_block block in
    let statement = unwrap_option (List.nth_opt block.statements (last_statement)) "unexpected" in
    let precondition = 
      match last_statement with
      | 0 -> 
        unwrap_option block.precondition "unexpected"
      | _ ->
        let statement = unwrap_option (List.nth_opt block.statements (last_statement - 1)) "unexpected" in
        unwrap_option (get_postcondition statement) "unexpected"
    in
    {
      cfg = cfg;
      last_block = last_block;
      last_statement = last_statement;
      trace = update_trace state.trace statement precondition
    }
  in
  let cfg = state.cfg in
  let current_block = Cfg.get_data cfg state.last_block in
  if state.last_statement = 0 then
    let map_fun idx =
      let block = Cfg.get_data cfg idx in
      let iteration_limit_reached = visit_limit block in
      let block = CfgBlock.update_formula_at_last block current_block.precondition in
      let block = CfgBlock.increase_visit_count block in
      let state = block_to_starting_state cfg idx block in
      if iteration_limit_reached then
        Either.Right(state)
      else
        Either.Left(state)
    in

    let next_states, end_states = List.partition_map map_fun (Cfg.pred_of cfg state.last_block) in
    match next_states with
    | [] -> [], state :: end_states
    | _ -> next_states, end_states
  else
    let block = block_analysis_step current_block state.last_statement in
    [ block_analysis_state cfg state.last_block (state.last_statement - 1) block ], []
