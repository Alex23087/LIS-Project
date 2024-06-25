module Prelude = Analysis_Prelude

(** {1 Data Structures}

Data structures used throughout the analysis. The submodules {{! DataStructures.Analysis}Analysis} and {{! DataStructures.Parser}Parser} specify
data structures used in those specific points of the software.
*)
module DataStructures = DataStructures

module CfgAnalysis = CfgAnalysis

(** {1 Formula Normalization}

This module implements functions to transform generic formulas into Existential Disjunctive Normal Form,
plus other utility functions to compute operations on normalized formulas.
*)
module Normalization = Normalization

(** {1 Expression Substitution}

This module provides functions to substitute identifiers with expressions in normalized formulas.
*)
module ExpressionSubstitution = ExpressionSubstitution

(** {1 Formula Simplification}

This module provides a general method for simplifying formulas according to equality rules of the logic operators.
Inner modules provide all the specific semplification functions.
*)
module FormulaSimplification = FormulaSimplification

(** {1 Atomic Analysis}

This module provides functions to analyze atomic commands, i.e. compute the pre-condition of an atomic command given a post-condition.
*)
module Atomic = Atomic

(** {1 Utility Functions}

A set of utility functions used throughout the analysis.
*)
module Utils = Analysis_Utils