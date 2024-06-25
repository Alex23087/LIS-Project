open DataStructures.Analysis
open NormalForm

(** p && true = p *)
let unit_and (formula: NormalForm.t) =
  let rec simplify_and formula = match formula with
    | Formula.And (f1, f2) ->
      let f1 = simplify_and f1 in
      let f2 = simplify_and f2 in
      if f1 = Formula.True then f2
      else if f2 = Formula.True then f1
      else Formula.And (f1, f2)
    | Formula.AndSeparately (f1, f2) -> Formula.AndSeparately (simplify_and f1, simplify_and f2)
    | _ -> formula in
  NormalForm.make formula.variables (List.map (simplify_and) formula.disjoints) formula.id_generator

let f = unit_and