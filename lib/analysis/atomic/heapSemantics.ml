open Analysis_Prelude
open NormalForm
open Atomic_Utils
open Formula

let alloc_heap_partition (formula : Formula.t) (vars : IdentifierSet.t) (id : identifier) (f : Formula.t -> bool) : Formula.t =  
  let and_list = expand_andSeparately formula in 
  let (matching_list, non_matching_list) = List.partition f and_list in 
  let t = compress_andSeparately non_matching_list in 
  match matching_list with 
  | [] -> 
    if ( 
      List.find_opt (function | True -> true | _ -> false ) non_matching_list |> 
      Option.is_some
    ) then formula else False
  | [_] -> 
    if check_frame_rule_side_condition t vars id then AndSeparately(EmptyHeap, t) 
    else False
  | _ -> False

let free_heap_partition (formula : Formula.t) (id : identifier) (f : Formula.t -> bool) (fresh_var : identifier) : Formula.t =  
  let and_list = expand_andSeparately formula in 
  try
    let (matching_list, non_matching_list) = List.partition f and_list in
    let t = compress_andSeparately non_matching_list in 
    match matching_list with 
    | [] -> 
      if ( 
        List.find_opt (function | True -> true | _ -> false ) non_matching_list |> 
        Option.is_some
      ) then AndSeparately(Allocation(id, (Variable(fresh_var))), t)
      else False
    | _ -> AndSeparately(Allocation(id, (Variable(fresh_var))), t)
  with 
  | Bound_Identifier(_) -> False (* bound identifier -> not handled; under-approximation *)

let write_heap_partition (formula : Formula.t) (id : identifier) (f : Formula.t -> bool) (fresh_var : identifier) : Formula.t =  
  let and_list = expand_andSeparately formula in 
  let (matching_list, non_matching_list) = List.partition f and_list in 
  let t = compress_andSeparately non_matching_list in 
  match matching_list with
  | [] ->
    if ( 
      List.find_opt (function | True -> true | _ -> false ) non_matching_list |> 
      Option.is_some
    ) then AndSeparately(Allocation(id, (Variable(fresh_var))), t) else False
  | [_] -> AndSeparately(Allocation(id, (Variable(fresh_var))), t)
  | _ -> False
  
let read_heap_partition (formula : Formula.t) (vars : IdentifierSet.t) (l_id : identifier) (r_id : identifier) (fresh_1 : identifier) (fresh_2 : identifier) (f : Formula.t -> bool) (is_x_free : bool) : Formula.t =  
  let and_list = expand_andSeparately formula in 
  let (matching_list, non_matching_list) = List.partition f and_list in
  match matching_list with
  | [] -> 
    if ( 
      List.find_opt (function | True -> true | _ -> false ) non_matching_list |> 
      Option.is_some 
    ) then (* True * t[fresh/x] * y -> fresh *)
      let t = (compress_andSeparately ((Allocation(r_id, Variable(fresh_1)))::non_matching_list)) in 
      substitute_expression_in_formula t (Variable(fresh_1)) l_id fresh_2
    else False
  | [Allocation(id,a) as matched] when id = r_id-> 
    let t = (compress_andSeparately non_matching_list) in
    let t' = AndSeparately(matched, substitute_expression_in_formula t a l_id fresh_2) in 
    let fv_a = get_free_identifiers a vars in 
    if is_identifier_free l_id fv_a
      then (if is_x_free then t' else formula)
    else False
  | _ -> False

(* apply alloc semantics to single formula *)
let apply_alloc (vars : IdentifierSet.t) (id : identifier) (post : Formula.t) : Formula.t = 
  match post with
  | True -> True
  | Allocation(x, _) when x = id  -> 
    if is_identifier_free x vars then EmptyHeap else False
  | AndSeparately(_, _) as formula -> 
    let f = function 
    | Allocation(x,_) when x=id -> 
      if is_identifier_free x vars then true else false
    | _ -> false in 
    alloc_heap_partition formula vars id f
  | _ -> False

(* apply free semantics to single formula *)
let apply_free (vars : IdentifierSet.t) (id : identifier) (fresh_var : identifier) (post : Formula.t) : Formula.t = 
  match post with
  | True -> AndSeparately(True, Allocation(id, (Variable(fresh_var))))
  | EmptyHeap -> False
  | NonAllocated(x) when x = id -> 
    if is_identifier_free x vars 
      then (Allocation(x, (Variable(fresh_var)))) 
    else False
  | AndSeparately(_, _) as formula -> 
    let f = function 
    | NonAllocated(x) when x=id -> 
      if is_identifier_free x vars then true 
      else raise (Bound_Identifier x) (* bound identifier -> not handled; under-approximation *)
    | _ -> false in 
    free_heap_partition formula id f fresh_var
  | _ -> False

(* apply write semantics to single formula *)
let apply_write (vars : IdentifierSet.t) (mem_id : identifier) (expr : 'a Ast.HeapRegularCommands.ArithmeticExpression.t) (fresh_var : identifier) (post : Formula.t) : Formula.t = 
  match post with
  | Allocation(x, y) when x = mem_id && equal_command_expression expr y -> 
    let ids = get_normal_form_expr_identifiers y in
    if is_identifier_free x vars && are_all_identifiers_free ids vars
      then (Allocation(x, (Variable(fresh_var))))
    else False
  | AndSeparately(_, _) as formula -> 
    let f = function 
      | Allocation(x, y) when x = mem_id && equal_command_expression expr y -> 
        let ids = get_normal_form_expr_identifiers y in
        if is_identifier_free x vars && are_all_identifiers_free ids vars
          then true else false
      | _ -> false
    in write_heap_partition formula mem_id f fresh_var
  | True -> True
  | _ -> False

(* apply read semantics to single formula *)
let apply_read (vars : IdentifierSet.t) (l_id : identifier) (r_id : identifier) (fresh_1 : identifier) (fresh_2 : identifier) (post : Formula.t) : Formula.t = 
  match post with
  | True -> True
  | Allocation(y, a) as formula when y = r_id -> 
    let fv_a = get_free_identifiers a vars in 
    if is_identifier_free y vars && is_identifier_free l_id fv_a
      then formula
    else False
  | AndSeparately(_, _) as formula -> 
    let f = function
      | Allocation(y, _) when y = r_id ->
        if is_identifier_free y vars then true else false
      | _ -> false
    in if is_identifier_free l_id vars 
      then read_heap_partition formula vars l_id r_id fresh_1 fresh_2 f true
    else read_heap_partition formula vars l_id r_id fresh_1 fresh_2 f false
  | _ -> False

(* apply the semantics of alloc using the extract_alloc util *)
let apply_alloc_v2 (x : identifier) (x': identifier) (vars : IdentifierSet.t) (disjoints : Formula.t list) =
  disjoints
  |> List.map (extract_alloc x x')
  |> List.concat
  |> List.filter (fun q' -> check_frame_rule_side_condition q' vars x)
  |> List.map (fun q' -> Formula.AndSeparately(EmptyHeap, q'))

(* apply the semantics of free using the extract_dealloc util *)
let apply_free_v2 (x : identifier) (new_name: identifier) (disjoints : Formula.t list) =
  disjoints
  |> List.map (extract_dealloc x)
  |> List.concat
  |> List.map (fun q' -> Formula.AndSeparately(Allocation(x, ArithmeticExpression.Variable new_name), q'))

(* apply the semantics of write using the extract_alloc util *)
let apply_write_v2 (x : identifier) (new_name: identifier) (disjoints : Formula.t list) =
  disjoints
  |> List.map (extract_alloc x new_name)
  |> List.concat
  |> List.map (fun q' -> Formula.AndSeparately(Allocation(x, ArithmeticExpression.Variable new_name), q'))

(* apply the semantics of read using the extract_alloc util *)
let apply_read_v2 (l_id : identifier) (r_id : identifier) (new_name: identifier) (new_name2: identifier) (disjoints : Formula.t list) =
  disjoints
  |> List.map (extract_alloc r_id new_name)
  |> List.concat
  |> List.map (fun q' -> Formula.AndSeparately(Allocation(r_id, ArithmeticExpression.Variable new_name), substitute_expression_in_formula q' (ArithmeticExpression.Variable new_name) l_id new_name2))
