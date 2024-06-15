open DataStructures.Analysis

let expression_simplification (formula: NormalForm.t) =
  let simplification_functs = [
    ExpressionSimplificationBase.f;
  ] in
  List.fold_left (|>) formula simplification_functs

let f = expression_simplification