open DataStructures
open DataStructures.Analysis
open NormalForm
open Analysis_Utils
open ExpressionSubstitution

let expr_is_var_or_constant (aexp: ArithmeticExpression.t) : bool =
  match aexp with
  | Variable(_) | Literal(_) -> true
  | _ -> false

let expr_is_var (x : identifier) (aexp : ArithmeticExpression.t) : bool =
  match aexp with
  | Variable(y) -> x = y
  | _ -> false

(* checks if var x is equal to another variable or a constant *)
let rec is_var_equated (x : identifier) (formula : Formula.t) : ArithmeticExpression.t option =
  match formula with
  | True -> Option.None
  | False -> Option.None
  | EmptyHeap -> Option.None
  | NonAllocated(_) -> Option.None
  | Allocation(_) -> Option.None
  | And(q1, q2)
  | AndSeparately(q1, q2) ->
    let r = is_var_equated x q1 in
    if Option.is_some r then r else is_var_equated x q2
  | Comparison(op, lexpr, rexpr) ->
    if op == BinaryComparison.Equals && expr_is_var x lexpr && not (expr_is_var x rexpr) && expr_is_var_or_constant rexpr then
      Some(rexpr)
    else if op == BinaryComparison.Equals && not (expr_is_var x lexpr) && expr_is_var x rexpr && expr_is_var_or_constant lexpr then
      Some(lexpr)
    else
      Option.None

(* for all disjuncts, if var x is equated to some other variable, perform the substitution *)
let replace_equated_var (x : identifier) (formula: NormalForm.t) : NormalForm.t =
  (* In theory this never uses the new name because substitutes a variable for a variable. However, I leave it here for safety since it gets removed by subsequent simplification steps *)
  let new_name, fresh_formula = generate_fresh_existentialized_variable formula in
  let replace_one_disjunct (disjoint : Formula.t) : Formula.t =
    match is_var_equated x disjoint with
    | Some(e) -> substitute_expression_in_formula disjoint e x new_name
    | None -> disjoint
  in
  NormalForm.make (fresh_formula.variables) (List.map replace_one_disjunct fresh_formula.disjoints) (fresh_formula.id_generator)

(** exists a . (a = b) && q = (b = b) && q\[b / a\] and analogously for and-separately *)
let bound_var_equal (formula: NormalForm.t) : NormalForm.t =
  IdentifierSet.fold replace_equated_var formula.variables formula

let f = bound_var_equal