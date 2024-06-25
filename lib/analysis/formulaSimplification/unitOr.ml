open DataStructures.Analysis
open NormalForm

(** p || false = p *)
let unit_or (formula: NormalForm.t) =
  let simplified_disjoints = List.filter (fun disjoint -> disjoint != Formula.False) formula.disjoints in
  let simplified_disjoints = if List.length simplified_disjoints = 0 then [Formula.False] else simplified_disjoints in
  NormalForm.make formula.variables simplified_disjoints formula.id_generator

let f = unit_or