open DataStructures.Analysis
open NormalForm

let removeIdentityComparisons (formula: NormalForm.t) =
  let is_equality_operator (op: BinaryComparison.t) =
    match op with
    | BinaryComparison.Equals
    | BinaryComparison.LessOrEqual
    | BinaryComparison.GreaterOrEqual -> true
    | _ -> false
  in
  let rec removeIdentityComparisons (formula: Formula.t) =
    match formula with
    | Comparison(op, lexpr, rexpr) when lexpr = rexpr ->
      if is_equality_operator op then
        Formula.True
      else
        Formula.False
    | And(lformula, rformula) ->
      And(removeIdentityComparisons lformula, removeIdentityComparisons rformula)
    | AndSeparately(lformula, rformula) ->
      AndSeparately(removeIdentityComparisons lformula, removeIdentityComparisons rformula)
    | _ -> formula
  in
  
  let disjoints = List.map removeIdentityComparisons formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = removeIdentityComparisons