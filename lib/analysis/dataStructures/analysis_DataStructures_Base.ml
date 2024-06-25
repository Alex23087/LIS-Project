open Base

type identifier = Ast.identifier [@@deriving show, sexp, compare, eq]
module AnnotatedNode = struct include Ast.AnnotatedNode end [@@deriving show]
module IdentifierSet = struct include Ast.IdentifierSet end [@@deriving show]

(** Position record, which holds where the given command or annotation is in the source files.*)
type position = {line: int; column: int} [@@deriving show, compare, sexp]

let make_position (line: int) (column: int) = {line; column}