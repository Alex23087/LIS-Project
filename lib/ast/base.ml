open Sexplib.Std
open Ppx_compare_lib.Builtin

(**{1 Support data structures}*)

(**Identifier type*)
type identifier = string [@@deriving show, sexp, compare, eq]

module AnnotatedNode = struct
  type ('a, 'b) t = {
    node: 'a;
    annotation: 'b
  } [@@deriving show, sexp, compare]
  let make (node: 'a) (annotation: 'b) = {node; annotation}
  let unpack (annotated_node: ('a, 'b) t) = (annotated_node.node, annotated_node.annotation)
  let annotation (annotated_node: ('a, 'b) t) = annotated_node.annotation
  let node (annotated_node: ('a, 'b) t) = annotated_node.node

  let update_annotation (annotated_node: ('a, 'b) t) (new_annot: 'b) =
    let node = node annotated_node in
    make node new_annot
  let update_node (annotated_node: ('a, 'b) t) (new_node: 'a) =
    let annot = annotation annotated_node in
    make new_node annot
end

(**IdentifierSet*)
module IdentifierSet = Set.Make(struct
  type t = identifier 
  let compare = compare
end)