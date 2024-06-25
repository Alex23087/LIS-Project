open DataStructures
open DataStructures.Analysis
open NormalForm
open ExpressionSimplificationUtils

let disequation_solver (formula: NormalForm.t) =
  let disequation_simplification (formula: Formula.t) =
    let is_useful_disequation (formula: Formula.t) (id: identifier) =
      let (op, lexpr, rexpr) = unpack_comparison formula in
      match op, lexpr, rexpr with
      | Equals, _, _ | NotEquals, _, _ -> false
      | _, Variable(x), Literal(_)
      | _, Literal(_), Variable(x) when x = id -> true
      | _ -> false
    in
    let extract_disequation (formula: Formula.t) =
      let (op, lexpr, rexpr) = unpack_comparison formula in
      match lexpr, rexpr with
      | Variable(var), Literal(value) -> op, var, value
      | Literal(value), Variable(var) -> invert_binary_comparison op, var, value
      | _ -> failwith "unexpected"
    in
    let convert_op_or_equal_comparisons (op, var, value: BinaryComparison.t * identifier * int) =
      match op with
      | LessOrEqual -> BinaryComparison.LessThan, var, value + 1
      | GreaterOrEqual -> BinaryComparison.GreaterThan, var, value - 1
      | _ -> op, var, value
    in
      
    let simplify_disequations (id: identifier) (comparisons, acc: Formula.t list * Formula.t list) =
      let comparisons, other = List.partition (fun x -> is_useful_disequation x id) comparisons in
      let comparisons = List.map (fun x -> x |> extract_disequation |> convert_op_or_equal_comparisons) comparisons in
      let lt_comparisons, gt_comparisons = List.partition_map (fun (op, _, value) -> if op = BinaryComparison.LessThan then Either.Left(value) else Either.Right(value)) comparisons in

      let acc =
        match lt_comparisons with
        | [] -> acc
        | xs -> 
          let lt_comparison = List.fold_left max (Int.min_int) xs in
          let lt_comparison = Formula.Comparison(BinaryComparison.LessThan, ArithmeticExpression.Variable(id), ArithmeticExpression.Literal(lt_comparison)) in
          lt_comparison :: acc
      in
      let acc =
        match gt_comparisons with
        | [] -> acc
        | xs -> 
          let gt_comparison = List.fold_left min (Int.max_int) xs in
          let gt_comparison = Formula.Comparison(BinaryComparison.GreaterThan, ArithmeticExpression.Variable(id), ArithmeticExpression.Literal(gt_comparison)) in
          gt_comparison :: acc
      in
      
      other, acc
    in

    let comparisons, others = unpack_conjuncts formula in
    let vars =
      List.map Analysis_Utils.get_normal_form_disjoint_identifiers comparisons |>
      List.fold_left (fun acc x -> IdentifierSet.union acc x) IdentifierSet.empty
    in
    let remainder, formulas = IdentifierSet.fold simplify_disequations vars (comparisons, others) in
    pack_conjuncts (remainder @ formulas)
  in

  let disjoints = List.map disequation_simplification formula.disjoints in
  NormalForm.make formula.variables disjoints formula.id_generator

let f = disequation_solver