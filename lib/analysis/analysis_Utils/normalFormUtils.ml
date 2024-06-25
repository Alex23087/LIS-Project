open DataStructures
open DataStructures.Analysis
open NormalForm

module VarMapKey = struct
  type t = identifier
  let compare = String.compare
end

module VarMap = Map.Make(VarMapKey)
type varMap = identifier VarMap.t

let fold mapping flist =
  let fold_fun (equal, mapping) f =
    match equal with
    | true -> f mapping
    | false -> false, mapping
  in
  List.fold_left fold_fun (true, mapping) flist

(** Checks whether two normalized formula are equal. *)
let equal_formulas (lformula: NormalForm.t) (rformula: NormalForm.t) =
  let rec flatten_conjunction (formula: Formula.t) =
    match formula with
    | And(lformula, rformula) -> flatten_conjunction lformula @ flatten_conjunction rformula
    | _ -> [formula]
  in
  let rec flatten_separate_conjunction (formula: Formula.t) =
    match formula with
    | AndSeparately(lformula, rformula) -> flatten_separate_conjunction lformula @ flatten_separate_conjunction rformula
    | _ -> [formula]
  in
  let rec equal_lists
    (cmpfn: ('a * IdentifierSet.t) -> ('a * IdentifierSet.t) -> varMap -> (bool * varMap))
    (llist, lbound: 'a list * IdentifierSet.t) (rlist, rbound: 'a list * IdentifierSet.t) (mapping: varMap)
  =
    match llist, rlist with
    | [], [] -> true, mapping
    | [], _::_ -> false, mapping
    | [l], [r] -> cmpfn (l, lbound) (r, rbound) mapping
    | l::llist, rlist -> (
      let f r =
        let same, mapping = cmpfn (l, lbound) (r, rbound) mapping in
        match same with
        | true -> Either.Left((mapping, r))
        | false -> Either.Right(r)
      in
      let r, rlist = List.partition_map f rlist in
      match r with
      | [] -> false, mapping
      | [(mapping, _)] -> equal_lists cmpfn (llist, lbound) (rlist, rbound) mapping
      | (mapping, _)::xs ->
        let xs = List.map snd xs in
        equal_lists cmpfn (llist, lbound) (xs @ rlist, rbound) mapping
    )
  in
  let equal_identifiers (lid, lbound: identifier * IdentifierSet.t) (rid, rbound: identifier * IdentifierSet.t) (mapping: varMap) =
    let l_is_free = IdentifierSet.find_opt lid lbound |> Option.is_none in      
    let r_is_free = IdentifierSet.find_opt rid rbound |> Option.is_none in
    match l_is_free, r_is_free with
    | true, true ->
      lid = rid, mapping
    | false, false -> (
      match VarMap.find_opt lid mapping with
      | Some(mapped_rid) when mapped_rid = rid -> true, mapping
      | Some(_) -> false, mapping
      | None -> true, VarMap.add lid rid mapping
    )
    | _ ->
      false, mapping
  in
  let rec equal_expressions (lexpr, lbound: ArithmeticExpression.t * IdentifierSet.t) (rexpr, rbound: ArithmeticExpression.t * IdentifierSet.t) (mapping: varMap) =
    match (lexpr, rexpr) with
    | (Literal(l), Literal(r)) ->
      l = r, mapping
    | (Variable(l), Variable(r)) ->
      equal_identifiers (l, lbound) (r, rbound) mapping
    | (Operation(lop, ll, lr), Operation(rop, rl, rr)) ->
      fold mapping [
        (fun mapping -> lop = rop, mapping);
        (equal_expressions (ll, lbound) (rl, rbound));
        (equal_expressions (lr, lbound) (rr, rbound))
      ]
    | _ ->
      false, mapping
  in
  let rec equal_disjoint (ldisjoint, lbound: Formula.t * IdentifierSet.t) (rdisjoint, rbound: Formula.t * IdentifierSet.t) (mapping: varMap) =
    match (ldisjoint, rdisjoint) with
    | True, True
    | False, False
    | EmptyHeap, EmptyHeap ->
      true, mapping
    | Allocation(lid, lexpr), Allocation(rid, rexpr) ->
      fold mapping [
        (equal_identifiers (lid, lbound) (rid, rbound));
        (equal_expressions (lexpr, lbound) (rexpr, rbound))
      ]
    | NonAllocated(lid), NonAllocated(rid) ->
      equal_identifiers (lid, lbound) (rid, rbound) mapping
    | Comparison(lop, ll, lr), Comparison(rop, rl, rr) ->
      fold mapping [
        (fun mapping -> lop = rop, mapping);
        (equal_expressions (ll, lbound) (rl, rbound));
        (equal_expressions (lr, lbound) (rr, rbound))
      ]
    | And(_), And(_) ->
      let ldisjoint = flatten_conjunction ldisjoint in
      let rdisjoint = flatten_conjunction rdisjoint in
      equal_lists equal_disjoint (ldisjoint, lbound) (rdisjoint, rbound) mapping
    | AndSeparately(_), AndSeparately(_) ->
      let ldisjoint = flatten_separate_conjunction ldisjoint in
      let rdisjoint = flatten_separate_conjunction rdisjoint in
      equal_lists equal_disjoint (ldisjoint, lbound) (rdisjoint, rbound) mapping
    | _ ->
      false, mapping
  in
  let equal_disjoints (ldisjoints: Formula.t list * IdentifierSet.t) (rdisjoints: Formula.t list * IdentifierSet.t) (mapping: varMap) =
    equal_lists equal_disjoint ldisjoints rdisjoints mapping
  in
  let equal, map = equal_disjoints (lformula.disjoints, lformula.variables) (rformula.disjoints, rformula.variables) VarMap.empty in 
  if equal = false then false
  else 
    IdentifierSet.map 
      (fun var -> (VarMap.find_opt var map |> Option.value) ~default:var) 
      (lformula.variables) |> 
      IdentifierSet.equal rformula.variables

(** Computes the set of identifiers in an arithmetic expression. *)
let rec get_normal_form_expr_identifiers (expr: ArithmeticExpression.t) =
  match expr with
  | Literal(_) -> (IdentifierSet.empty)
  | Variable(id) -> (IdentifierSet.singleton id)
  | Operation(_, lexpr, rexpr) ->
    let l_ids = get_normal_form_expr_identifiers lexpr in
    let r_ids = get_normal_form_expr_identifiers rexpr in
    IdentifierSet.union l_ids r_ids

(** Computes the set of identifiers in a Normal Form disjoint. *)
let rec get_normal_form_disjoint_identifiers (formula: Formula.t) =
  match formula with
  | True | False | EmptyHeap ->
    IdentifierSet.empty
  | Allocation(id, expr) -> IdentifierSet.add id (get_normal_form_expr_identifiers expr)
  | NonAllocated(id) -> IdentifierSet.singleton id
  | Comparison(_, lexpr, rexpr) ->
    IdentifierSet.union (get_normal_form_expr_identifiers lexpr) (get_normal_form_expr_identifiers rexpr)
  | And(lformula, rformula) | AndSeparately(lformula, rformula) ->
    IdentifierSet.union (get_normal_form_disjoint_identifiers lformula) (get_normal_form_disjoint_identifiers rformula)

(** Computes the set of free variables in a normalized formula.

The set of free variables is the set of all the variables occurring in the formula minus the set
of bound (existentialized) variables.
*)
let normal_form_free_variables (formula: NormalForm.t) =
  let ids = List.map get_normal_form_disjoint_identifiers formula.disjoints in
  let ids = List.fold_left (fun acc ids -> IdentifierSet.union acc ids) IdentifierSet.empty ids in
  IdentifierSet.diff ids formula.variables

let update_id_generator (id_generator: NormalForm.id_generator) =
  {first_id = id_generator.first_id; last_id = id_generator.last_id + 1}