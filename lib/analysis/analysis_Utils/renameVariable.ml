open DataStructures
open DataStructures.Analysis
open NormalForm
open NormalFormUtils

let new_variable_name (old_var: identifier) (id_generator: id_generator) =
  let substr = String.split_on_char '$' old_var in
  if List.length substr > 2 then
    raise (Failure "Found more than two $ characters in a variable name")
  else if List.length substr = 2 then
    let var_name = List.nth substr 1 in
    ((string_of_int id_generator.last_id) ^ "$" ^ var_name, update_id_generator id_generator)
  else
    let var_name = List.hd substr in
    ((string_of_int id_generator.last_id) ^ "$" ^ var_name, update_id_generator id_generator)

let rename_variable_in_set (variables: IdentifierSet.t) (var: identifier) (new_name: identifier) =
  match IdentifierSet.find_opt var variables with
  | Some(_) -> IdentifierSet.add new_name (IdentifierSet.remove var variables)
  | None -> variables

let rec rename_variable_in_formula (disjoint: Formula.t) (var: identifier) (new_name: identifier) =
  let rename_variable_name (var: identifier) (old_name: identifier) (new_name: identifier) =
    if var = old_name then new_name else var
  in
  let rec rename_variable_in_expression (expr: ArithmeticExpression.t) (var: identifier) (new_name: identifier) =
    match expr with
    | Literal(_) -> expr
    | Variable(id) -> ArithmeticExpression.Variable(rename_variable_name id var new_name)
    | Operation(op, lexpr, rexpr) ->
      let lexpr = rename_variable_in_expression lexpr var new_name in
      let rexpr = rename_variable_in_expression rexpr var new_name in
      ArithmeticExpression.Operation(op, lexpr, rexpr)
  in

  match disjoint with
  | True | False | EmptyHeap ->
    disjoint
  | NonAllocated(id) ->
    Formula.NonAllocated(rename_variable_name id var new_name)
  | And(lformula, rformula) ->
    let lformula = rename_variable_in_formula lformula var new_name in
    let rformula = rename_variable_in_formula rformula var new_name in
    Formula.And(lformula, rformula)
  | Comparison(op, lexpr, rexpr) ->
    let lexpr = rename_variable_in_expression lexpr var new_name in
    let rexpr = rename_variable_in_expression rexpr var new_name in
    Formula.Comparison(op, lexpr, rexpr)
  | Allocation(id, expr) ->
    let id = rename_variable_name id var new_name in
    let expr = rename_variable_in_expression expr var new_name in
    Formula.Allocation(id, expr)
  | AndSeparately(lformula, rformula) ->
    let lformula = rename_variable_in_formula lformula var new_name in
    let rformula = rename_variable_in_formula rformula var new_name in
    Formula.AndSeparately(lformula, rformula)
and rename_variable_in_disjoints (var: identifier) (variables: IdentifierSet.t) (disjoints: Formula.t list) (id_generator: id_generator) =
  let (new_var, id_generator) = new_variable_name var id_generator in
  let variables = IdentifierSet.add new_var (IdentifierSet.remove var variables) in
  let disjoints = List.map (fun x -> rename_variable_in_formula x var new_var) disjoints in
  (variables, disjoints, id_generator)
and rename_variable_in_normal_form (formula: NormalForm.t) (variable: identifier) =
  let (variables, disjoints, last_id_generator) = 
    rename_variable_in_disjoints variable formula.variables formula.disjoints formula.id_generator in
  NormalForm.make variables disjoints last_id_generator

let rename_variables_in_normal_form (formula: NormalForm.t) (variables: identifier list) =
  List.fold_left (fun acc x -> rename_variable_in_normal_form acc x) formula variables

(** Generate a fresh identifier and bind it in the formula
@param formula the formula to update
@return a pair containing a fresh variable and the updated formula
*)
let generate_fresh_existentialized_variable (formula: NormalForm.t) =
  let fresh_var_name = "#fresh_var" in
  let (fresh_var_name, id_generator) = new_variable_name fresh_var_name formula.id_generator in
  let variables = IdentifierSet.add fresh_var_name formula.variables in
  fresh_var_name, NormalForm.make variables formula.disjoints id_generator
