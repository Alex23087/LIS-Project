open DataStructures
open DataStructures.Analysis
open DataStructures.Parser
open Analysis_Utils

let annot_cmd command =
  let annotation = Commands.make_annotation 0 0 None in
  annotate command annotation

let annot formula =
  let annotation = LogicFormulas.make_annotation 0 0 in
  annotate formula annotation

(* Check the number of expected bound variables *)
let test_expected_bound_variables (normalized: NormalForm.t) (num_bound_vars: int) =
  if IdentifierSet.cardinal normalized.variables = num_bound_vars then
    true
  else
    let _ = if IdentifierSet.is_empty normalized.variables then
      print_endline "actual identifiers: None"
    else
      print_endline "actual identifiers: ";
      IdentifierSet.iter print_endline normalized.variables
    in
    false

(* print a list of formulas *)
let print_formulas lst =
  print_endline "actual disjoints: ";
  List.iter (fun item -> print_endline (NormalForm.Formula.show item)) lst

(* [test_expected_disjoints formula expected bound_name] checks that the list of actual disjoints in [formula]
  is the same of [expected] disjoints. [bound_names] is the set of bound names of the expected disjoints, which are
  unified with the names in the actual formula, as two formulas are equal up to alpha-conversion (bound names renaming). *)
let test_expected_disjoints (normalized: NormalForm.t) (expected: NormalForm.Formula.t list) (bound_names: identifier list) =
  let bound_names = IdentifierSet.of_list bound_names in
  let expected = NormalForm.make bound_names expected {first_id = 0; last_id = 0} in
  equal_formulas normalized expected

let rec foldi i f acc =
  if i <= 0 then acc else foldi (pred i) f (f acc)

(* Alias for better readability *)
module Commands = Ast.HeapRegularCommands
module PFormula = DataStructures.Parser.LogicFormulas.Formula
module PBinaryComparison = DataStructures.Parser.LogicFormulas.BinaryComparison
module PArithmeticExpression = DataStructures.Parser.LogicFormulas.ArithmeticExpression
module PBinaryOperator = DataStructures.Parser.LogicFormulas.BinaryOperator