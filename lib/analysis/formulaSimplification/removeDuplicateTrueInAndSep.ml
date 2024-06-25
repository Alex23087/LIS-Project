open DataStructures.Analysis
open NormalForm

(** p * true * true = p * true *)
let remove_duplicate_trues (formula: NormalForm.t) =
  let rec unpack_separate_conjuncts (formula: Formula.t) =
    match formula with
    | AndSeparately(lformula, rformula) ->
      unpack_separate_conjuncts lformula @ unpack_separate_conjuncts rformula
    | _ -> [formula]
  in
  let rec pack_separate_conjuncts (formulas: Formula.t list) =
    match formulas with
    | [] -> failwith "unexpected"
    | [x] -> x
    | x::xs -> Formula.AndSeparately(x, pack_separate_conjuncts xs)
  in
  let rec remove_duplicate_trues (formula: Formula.t) =
    match formula with
    | AndSeparately(_) ->
      let conjuncts = unpack_separate_conjuncts formula in
      let conjuncts = List.map remove_duplicate_trues conjuncts in
      let trues, other = List.partition (fun x -> x = Formula.True) conjuncts in
      let conjuncts = 
        match trues with
        | [] -> other
        | _ -> Formula.True :: other
      in
      pack_separate_conjuncts conjuncts
    | And(lformula, rformula) ->
      Formula.And(remove_duplicate_trues lformula, remove_duplicate_trues rformula)
    | _ -> formula
  in

  let disjoints = List.map remove_duplicate_trues formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = remove_duplicate_trues