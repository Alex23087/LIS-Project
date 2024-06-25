open DataStructures.Analysis
open NormalForm

(** p * emp = p *)
let unit_and_sep (formula: NormalForm.t) =
  let rec simplify_and_sep formula = match formula with
    | Formula.AndSeparately (f1, f2) ->
      let f1 = simplify_and_sep f1 in
      let f2 = simplify_and_sep f2 in
      if f1 = Formula.EmptyHeap then f2
      else if f2 = Formula.EmptyHeap then f1
      else Formula.AndSeparately (f1, f2)
    | Formula.And (f1, f2) -> Formula.And (simplify_and_sep f1, simplify_and_sep f2)
    | _ -> formula in
  NormalForm.make formula.variables (List.map (simplify_and_sep) formula.disjoints) formula.id_generator

let f = unit_and_sep