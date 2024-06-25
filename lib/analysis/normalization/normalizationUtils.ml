open DataStructures
open DataStructures.Analysis
open NormalForm
open Analysis_Utils

let rec remove_annotation_in_formula (formula: 'a Ast.AnnotationLogic.t) : Formula.t =
  match formula.node with
  | True -> Formula.True
  | False -> Formula.False
  | And(left, right) -> 
    let left = remove_annotation_in_formula left in
    let right = remove_annotation_in_formula right in
    Formula.And(left, right)
  | AndSeparately(left, right) -> 
    let left = remove_annotation_in_formula left in
    let right = remove_annotation_in_formula right in
    Formula.AndSeparately(left, right)
  | Comparison(op, lexpr, rexpr) ->
    let lexpr = remove_annotation_in_expr lexpr in
    let rexpr = remove_annotation_in_expr rexpr in
    Formula.Comparison(op, lexpr, rexpr)
  | EmptyHeap -> Formula.EmptyHeap
  | NonAllocated(id) -> Formula.NonAllocated(id)
  | Allocation(id, expr) -> Formula.Allocation(id, (remove_annotation_in_expr expr))
  | Exists(_, _) -> raise (Failure "Existentialization of identifiers does not appear in normalized formulas")
  | Or(_, _) -> raise (Failure "Disjunctions of formulas does not appear in normalized formulas")
and remove_annotation_in_expr expr =
  match expr.node with
  | Literal(value) -> ArithmeticExpression.Literal(value)
  | Variable(id) -> ArithmeticExpression.Variable(id)
  | Operation(op, lexpr, rexpr) ->
    let lexpr = remove_annotation_in_expr lexpr in
    let rexpr = remove_annotation_in_expr rexpr in
    ArithmeticExpression.Operation(op, lexpr, rexpr)

let rename_variable_in_disjoints elem (variables, disjoints, id_generator) =
  rename_variable_in_disjoints elem variables disjoints id_generator

let rename_common_free_variables (lformula: NormalForm.t) (rformula: NormalForm.t) (last_id_generator: id_generator) =
  let lformula_free, lformula_bound = normal_form_free_variables lformula, lformula.variables in
  let rformula_free, rformula_bound = normal_form_free_variables rformula, rformula.variables in

  (* rename the bound variables in lformula that are free in rformula *)
  let lformula_vars_to_rename = IdentifierSet.inter lformula_bound rformula_free in
  let (variables, disjoints, last_id_generator) =
    IdentifierSet.fold rename_variable_in_disjoints lformula_vars_to_rename (lformula.variables, lformula.disjoints, last_id_generator)
  in
  let lformula = NormalForm.make variables disjoints last_id_generator in

  (* rename the bound variables in rformula that are free in lformula *)
  let rformula_vars_to_rename = IdentifierSet.inter rformula_bound lformula_free in
  let (variables, disjoints, last_id_generator) =
    IdentifierSet.fold rename_variable_in_disjoints rformula_vars_to_rename (rformula.variables, rformula.disjoints, last_id_generator)
  in
  let rformula = NormalForm.make variables disjoints last_id_generator in

  (* rename the common bound variables only in the rformulas (it would have been indifferent if they were renamed in lformulas) *)
  let common_vars_to_rename = IdentifierSet.inter lformula_bound rformula_bound in
  let (variables, disjoints, last_id_generator) =
    IdentifierSet.fold rename_variable_in_disjoints common_vars_to_rename (rformula.variables, rformula.disjoints, last_id_generator)
  in
  let rformula = NormalForm.make variables disjoints last_id_generator in
  (lformula, rformula, last_id_generator)

let greatest_id_generator (lformula: NormalForm.t) (rformula: NormalForm.t) =
  let lgen, rgen = lformula.id_generator, rformula.id_generator in
  {first_id = min lgen.first_id rgen.first_id; last_id = max lgen.last_id rgen.last_id}

let rename_common_bound_variables (lformula: NormalForm.t) (rformula: NormalForm.t) =
  let last_id_generator = greatest_id_generator lformula rformula in
  if lformula.id_generator.last_id < rformula.id_generator.first_id then
    rformula, last_id_generator
  else
    let common_vars_to_rename = IdentifierSet.inter lformula.variables rformula.variables in
    let (variables, disjoints, last_id_generator) =
      IdentifierSet.fold rename_variable_in_disjoints common_vars_to_rename (rformula.variables, rformula.disjoints, last_id_generator)
    in
    let rformula = NormalForm.make variables disjoints last_id_generator in
    rformula, last_id_generator

let merge_two_formulas (lformula: NormalForm.t) (rformula: NormalForm.t) make_disjoints =
  let rformula, last_id_generator = rename_common_bound_variables lformula rformula in
  let (lformula, rformula, last_id_generator) = rename_common_free_variables lformula rformula last_id_generator in
  let bound_variables = IdentifierSet.union lformula.variables rformula.variables in
  let disjoints = make_disjoints lformula rformula in
  NormalForm.make bound_variables disjoints last_id_generator