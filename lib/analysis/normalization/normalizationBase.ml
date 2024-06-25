open DataStructures
open DataStructures.Analysis
open NormalForm
open NormalizationMethods
open NormalizationUtils

(** [existential_disjuntive_normal_form] [formula] converts a [formula] in Existential Disjunctive Normal Form. *)
let existential_disjuntive_normal_form (formula: 'a Ast.AnnotationLogic.t) = 
  let rec existential_disjuntive_normal_form (formula: 'a Ast.AnnotationLogic.t) (id_generator: NormalForm.id_generator) =
    match formula.node with
    | True | False | EmptyHeap | NonAllocated(_)
    | Comparison(_, _, _) | Allocation(_, _) ->
      let formula = remove_annotation_in_formula formula in
      NormalForm.make IdentifierSet.empty [formula] id_generator
    | And(lformula, rformula) ->
      (* normalize recursively *)
      let lformula = existential_disjuntive_normal_form lformula id_generator in
      let rformula = existential_disjuntive_normal_form rformula lformula.id_generator in
      conjunction_of_normalized_formulas lformula rformula
    | AndSeparately(lformula, rformula) ->
      (* normalize recursively *)
      let lformula = existential_disjuntive_normal_form lformula id_generator in
      let rformula = existential_disjuntive_normal_form rformula lformula.id_generator in
      separate_conjunction_of_normalized_formulas lformula rformula
    | Exists(id, subformula) ->
      (* normalize recursively *)
      let subformula = existential_disjuntive_normal_form subformula id_generator in
      existentialization_of_identifier id subformula
    | Or(lformula, rformula) ->
      (* normalize recursively *)
      let lformula = existential_disjuntive_normal_form lformula id_generator in
      let rformula = existential_disjuntive_normal_form rformula lformula.id_generator in
      disjunction_of_normalized_formulas lformula rformula
  in
  existential_disjuntive_normal_form formula {first_id = 0; last_id = 0}
(** [existential_disjuntive_normal_expr] [expr] transforms the given arithmetic expression [expr] in Normal Form *)
let existential_disjuntive_normal_expr (expr: 'a Ast.AnnotationLogic.ArithmeticExpression.t) =
  remove_annotation_in_expr expr