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
      let new_name, fresh_post_condition = generate_fresh_existentialized_variable post_condition in
      let disjoints = apply_alloc_v2 id new_name fresh_post_condition.variables fresh_post_condition.disjoints in
      make (fresh_post_condition.variables) disjoints (fresh_post_condition.id_generator)
    | Free(id) ->
      let new_name, fresh_post_condition = generate_fresh_existentialized_variable post_condition in
      let disjoints = apply_free_v2 id new_name post_condition.disjoints in
      make (fresh_post_condition.variables) disjoints (fresh_post_condition.id_generator)
    | WriteHeap(mem_id, _) ->
      let new_name, fresh_post_condition = generate_fresh_existentialized_variable post_condition in
      let disjoints = apply_write_v2 mem_id new_name post_condition.disjoints in
      make (fresh_post_condition.variables) disjoints (fresh_post_condition.id_generator)
    | ReadHeap(l_id, r_id) ->
      let new_name, fresh_post_condition = generate_fresh_existentialized_variable post_condition in
      let new_name2, fresh_post_condition2 = generate_fresh_existentialized_variable fresh_post_condition in
      let disjoints = apply_read_v2 l_id r_id new_name new_name2 fresh_post_condition2.disjoints in
      make (fresh_post_condition2.variables) disjoints (fresh_post_condition2.id_generator)

  in simplify_formula precondition
