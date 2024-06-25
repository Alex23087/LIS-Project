open DataStructures
open DataStructures.Analysis
open NormalForm
open Analysis_Utils

(** Remove bound variables that do not appear in the formula. *)
let bound_variable_cleanup (formula: NormalForm.t) =
  let fold_fun acc formula = IdentifierSet.union acc (get_normal_form_disjoint_identifiers formula) in
  let all_variables = List.fold_left fold_fun IdentifierSet.empty formula.disjoints in
  let actual_bound_variables = IdentifierSet.inter all_variables formula.variables in
  NormalForm.make actual_bound_variables formula.disjoints formula.id_generator

let f = bound_variable_cleanup