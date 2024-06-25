open NormalizationBase
open DataStructures.Analysis.NormalForm

open Analysis_TestUtils

(* Alias for better readability *)
module PFormula = DataStructures.Parser.LogicFormulas.Formula

let%test "existentialized non bound variable" =
  let formula = annot (
    PFormula.Exists("x", annot (
      PFormula.Exists("y", annot (
        PFormula.NonAllocated("x")
      ))
    ))
  )
  in
  let normalized = existential_disjuntive_normal_form formula in
  let expected_disjoints =
    Formula.NonAllocated("x") :: []
  in
  test_expected_bound_variables normalized 1 &&
  test_expected_disjoints normalized expected_disjoints ["x"]

let%test "disjoint merging" =
  let formula = annot (
    PFormula.Or(annot(
      PFormula.Or(annot (
        PFormula.NonAllocated("x")
      ), annot (
        PFormula.NonAllocated("y")
      ))
    ), annot (PFormula.Or(annot (
      PFormula.NonAllocated("z")
      ), annot (
        PFormula.NonAllocated("w")
      ))
    ))
  ) in
  let normalized = existential_disjuntive_normal_form formula in
  let expected_disjoints = 
    Formula.NonAllocated("x") :: 
    Formula.NonAllocated("y") :: 
    Formula.NonAllocated("z") :: 
    Formula.NonAllocated("w") :: []
  in
  test_expected_bound_variables normalized 0 &&
  test_expected_disjoints normalized expected_disjoints []

let%test "and distribution" =
  let formula = annot (
    PFormula.And(annot(
      PFormula.Or(annot (
        PFormula.NonAllocated("x")
      ), annot (
        PFormula.NonAllocated("y")
      ))
    ), annot (PFormula.Or(annot (
      PFormula.NonAllocated("z")
      ), annot (
        PFormula.NonAllocated("w")
      ))
    ))
  ) in 
  let normalized = existential_disjuntive_normal_form formula in
  let expected_disjoints = Formula.And(
    Formula.NonAllocated("x"),
    Formula.NonAllocated("z")
  ) ::  Formula.And(
    Formula.NonAllocated("x"),
    Formula.NonAllocated("w")
  ) ::  Formula.And(
    Formula.NonAllocated("y"),
    Formula.NonAllocated("z")
  ) ::  Formula.And(
    Formula.NonAllocated("y"),
    Formula.NonAllocated("w")
  ) :: []
  in
  test_expected_bound_variables normalized 0 &&
  test_expected_disjoints normalized expected_disjoints []

let%test "and separately distribution" =
  let formula = annot (
    PFormula.AndSeparately(annot(
      PFormula.Or(annot (
        PFormula.NonAllocated("x")
      ), annot (
        PFormula.NonAllocated("y")
      ))
    ), annot (PFormula.Or(annot (
      PFormula.NonAllocated("z")
      ), annot (
        PFormula.NonAllocated("w")
      ))
    ))
  ) in 
  let normalized = existential_disjuntive_normal_form formula in
  let expected_disjoints = Formula.AndSeparately(
    Formula.NonAllocated("x"),
    Formula.NonAllocated("z")
  ) ::  Formula.AndSeparately(
    Formula.NonAllocated("x"),
    Formula.NonAllocated("w")
  ) ::  Formula.AndSeparately(
    Formula.NonAllocated("y"),
    Formula.NonAllocated("z")
  ) ::  Formula.AndSeparately(
    Formula.NonAllocated("y"),
    Formula.NonAllocated("w")
  ) :: []
  in
  test_expected_bound_variables normalized 0 &&
  test_expected_disjoints normalized expected_disjoints []

let%test "variables renaming when merging normalized forms" =
  let formula = annot (
    PFormula.AndSeparately(
      annot (PFormula.Exists("y",
        annot (PFormula.Exists("x", 
          annot (PFormula.And(
            annot (PFormula.NonAllocated("x")), 
            annot (PFormula.NonAllocated("y"))
          ))
        ))
      )),
      annot (PFormula.Or(
        annot (PFormula.Exists("x",
          annot (PFormula.NonAllocated("x"))
        )),
        annot (PFormula.NonAllocated("y"))
      ))
    )
  ) in 
  let normalized = existential_disjuntive_normal_form formula in
  let expected_disjoints =
    Formula.AndSeparately(
      Formula.And(
        Formula.NonAllocated("x"),
        Formula.NonAllocated("a")
      ),
      Formula.NonAllocated("b")
    ) ::
    Formula.AndSeparately(
      Formula.And(
        Formula.NonAllocated("x"),
        Formula.NonAllocated("a")
      ),
      Formula.NonAllocated("y")
    ) :: []
  in
  test_expected_bound_variables normalized 3 &&
  test_expected_disjoints normalized expected_disjoints ["a"; "b"; "x"]