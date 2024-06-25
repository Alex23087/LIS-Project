open DataStructures
open DataStructures.Analysis
open NormalForm

let rec get_heap_identifiers (formula: Formula.t) =
  match formula with
  | True | False | EmptyHeap | Comparison _ ->
    IdentifierSet.empty
  | Allocation(id, _) | NonAllocated(id) ->
    IdentifierSet.singleton id
  | And(lformula, rformula) | AndSeparately(lformula, rformula) ->
    IdentifierSet.union (get_heap_identifiers lformula) (get_heap_identifiers rformula)

(** x -> w * x -> z = false *)
let no_shared_ids (formula: NormalForm.t) =
  let rec are_separated formula = match formula with
    | Formula.AndSeparately (f1, f2) ->
      (* poor man's short circuiting *)
      let is_ok = are_separated f1 in
      let is_ok = is_ok && are_separated f2 in
      if is_ok then
        let f1_identifiers = get_heap_identifiers f1 in
        let f2_identifiers = get_heap_identifiers f2 in
        IdentifierSet.disjoint f1_identifiers f2_identifiers
      else false
    | Formula.And (f1, f2) -> are_separated f1 && are_separated f2
    | _ -> true in
  (* because there are only and\and separately, falseness propagates to the top *)
  let new_disjoints = List.map (fun disjoint -> if are_separated disjoint then disjoint else Formula.False) formula.disjoints in
  NormalForm.make formula.variables new_disjoints formula.id_generator

let f = no_shared_ids