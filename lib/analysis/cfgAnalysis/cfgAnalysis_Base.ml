open DataStructures.Analysis
open CfgAnalysis_Utils

let analyze_program (cfg: Cfg.t) =
  let states = starting_states cfg in
  let rec analyze (next_states: analysis_state list) (end_states: analysis_state list) =
    match next_states with
    | [] ->
      end_states
    | hd::tl ->
      let next_states, new_end_states = analysis_step hd in
      analyze (next_states @ tl) (new_end_states @ end_states)
  in
  analyze states []
