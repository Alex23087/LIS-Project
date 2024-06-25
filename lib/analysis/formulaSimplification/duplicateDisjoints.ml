open DataStructures.Analysis
open NormalForm

let remove_duplicate_disjoints (formula: NormalForm.t) =
  let rec remove_duplicates (acc: Formula.t list) (disjoints: Formula.t list) =
    match disjoints with
    | x::xs ->
      let not_equals = List.filter (fun y -> x <> y) xs in
      remove_duplicates (x::acc) not_equals
    | _ -> acc @ disjoints
    in
  let disjoints = remove_duplicates [] formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = remove_duplicate_disjoints