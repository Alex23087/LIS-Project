open DataStructures.Analysis
open NormalForm

(** p && false = false *)
let zero_and (formula: NormalForm.t) =
  let rec simplify_and formula = match formula with
    | Formula.And (f1, f2) as f ->
      let f1 = simplify_and f1 in
      let f2 = simplify_and f2 in
      if f1 = Formula.False || f2 = Formula.False
        then Formula.False
        else f
    | Formula.AndSeparately (f1, f2) -> Formula.AndSeparately (simplify_and f1, simplify_and f2)
    | _ -> formula in
  NormalForm.make formula.variables (List.map (simplify_and) formula.disjoints) formula.id_generator

let f = zero_and