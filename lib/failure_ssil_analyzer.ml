(**{1 FAILURE Analyzer}*)

(**Definition of generic Abstract Syntax Trees to represent our programs*)
module Ast = Ast

(**Definition of Control Flow Graph data structures to represent our program*)
module Cfg = Cfg

(**Definition of the data structures used to represent the results of the analysis*)
module Parserlexer = Parser_lexer

(***)
module Analysis = Analysis

(**One module to import all the data structures used throughout the analisys tool*)
module Prelude = Prelude
