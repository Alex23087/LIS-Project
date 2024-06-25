open Analysis_Prelude
open NormalForm
open HeapSemantics
open Ast.HeapRegularCommands

(** Computes the pre-condition of the given atomic command and post-condition.
    Each disjunction is handled indipendentely (disj rule)
 *)
let compute_precondition (command: 'a HeapAtomicCommand.t) (post_condition: NormalForm.t) : NormalForm.t =
  let precondition = 
    match command.node with
    | Skip ->
      post_condition
    | Assignment(id, expr) ->
      let expr = command_expression_to_logic_expression expr (fun _ -> ()) in
      let expr = existential_disjuntive_normal_expr expr in
      let expr_vars = Analysis_Utils.get_normal_form_expr_identifiers expr in
      let rename_vars = IdentifierSet.inter post_condition.variables expr_vars |> IdentifierSet.elements in
      let post_condition = Analysis_Utils.rename_variables_in_normal_form post_condition rename_vars in
      substitute_expression_in_normalized_formula post_condition expr id
    | NonDet(id) ->
      existentialization_of_identifier id post_condition
    | Guard(expr) ->
      let formula = command_bexpression_to_logic_formula expr (fun _ -> ()) in
      let formula = existential_disjuntive_normal_form formula in
      conjunction_of_normalized_formulas formula post_condition
    | Allocation(id) -> 
      let disjoints = List.map (apply_alloc (post_condition.variables) id) (post_condition.disjoints) in
      make (post_condition.variables) disjoints (post_condition.id_generator)
    | Free(id) -> 
      let f (list, pc) dj = 
        let name, pc = generate_fresh_existentialized_variable pc in
        ((name, dj)::list, pc) in
      let (l, fresh_post_condition) = 
        List.fold_left f ([], post_condition) post_condition.disjoints in
      let disjoints = 
        List.map (fun (x,y) -> apply_free (fresh_post_condition.variables) id x y) l in
      make (fresh_post_condition.variables) disjoints (fresh_post_condition.id_generator)
    | WriteHeap(mem_id, expr) ->
      let f (list, pc) dj = 
        let name, pc = generate_fresh_existentialized_variable pc in
        ((name, dj)::list, pc) in
      let (l, fresh_post_condition) = 
        List.fold_left f ([], post_condition) post_condition.disjoints in
      let disjoints = 
        List.map (fun (x,y) -> apply_write (fresh_post_condition.variables) mem_id expr x y) l in
      make (fresh_post_condition.variables) disjoints (fresh_post_condition.id_generator)
    | ReadHeap(l_id, r_id) -> 
      let fn1, pc = generate_fresh_existentialized_variable post_condition in 
      let fn2, pc = generate_fresh_existentialized_variable pc in 
      let l = List.map (apply_read pc.variables l_id r_id fn1 fn2 ) pc.disjoints in
      make (pc.variables) l (pc.id_generator)
  in simplify_formula precondition
