open Ast.HeapRegularCommands
open Cfg_Node

module Converter = struct

  (** Converts the AST into the CFG composed by nodes. The resulting structure
      might not be the smallest rappresentation possible. No node has more than
      one HeapAtomicCommand in the exp list.
   *)
  let rec convert_helper(root: 'a HeapRegularCommand.t) :
            'a HeapAtomicCommand.t list Node.t *
              'a HeapAtomicCommand.t list Node.t ref =
    match root.node with
    | Command(atom) ->
       let atom = Ast.AnnotatedNode.update_annotation atom root.annotation in
       let newcommand = Node.make [atom] [] [] in
       (newcommand, ref newcommand)
    | Sequence(comm1, comm2) ->
       let ((root1, end1), (root2, end2)) = (convert_helper comm1, convert_helper comm2) in
       Node.add_succ !end1 root2;
       (root1, end2)
    | NondeterministicChoice(comm1, comm2) ->
       let ((root1, end1), (root2, end2)) = (convert_helper comm1, convert_helper comm2) in
       let dummyentry = Node.make [] [] [] in
       let dummyexit  = Node.make [] [] [] in
       Node.add_succ dummyentry root1;
       Node.add_succ dummyentry root2;
       Node.add_succ !end1 dummyexit;
       Node.add_succ !end2 dummyexit;
       (dummyentry, ref dummyexit)
    | Star(comm) ->
       let (root1, end1) = convert_helper comm in
       let dummyentry = Node.make [] [] [] in
       let dummyexit  = Node.make [] [] [] in
       Node.add_succ dummyentry dummyexit;
       Node.add_succ dummyentry root1;
       Node.add_succ !end1 dummyexit;
       Node.add_succ !end1 root1;
       (dummyentry, ref dummyexit)

  (** Groups up consecutive nodes by appending the exp to the first.
      If keep_structure == true then only if the exp have the same instruction
      they would be grouped up.
   *)
  let simplify (keep_structure: bool) (root: 'a HeapAtomicCommand.t list Node.t) : unit =
    let alreadyvisited = ref [] in

    let rec remove_and_recurse (root: 'a HeapAtomicCommand.t list Node.t) (succ: 'a HeapAtomicCommand.t list Node.t) (keep_structure: bool) : unit =
      Node.set_exp root ((Node.get_exp root) @ (Node.get_exp succ));
      Node.set_succ root (Node.get_succ succ);
      List.iter (fun x -> Node.remove_pred x (Node.get_id succ)) (Node.get_succ succ);
      alreadyvisited := List.filter ((!=) (Node.get_id root)) !alreadyvisited;
      help_simplify keep_structure root
    and help_simplify (keep_structure: bool) (root: 'a HeapAtomicCommand.t list Node.t) : unit =
      (* check that we haven't already visited the node *)
      if List.mem (Node.get_id root) !alreadyvisited then
        ()
      else (
        (* add it to the visited nodes *)
        alreadyvisited := (Node.get_id root) :: !alreadyvisited;
        match Node.get_succ root with
        | [] -> () (* at the end, we have nothing else to simplify *)
        | [succ] when Node.get_id succ != Node.get_id root -> (
          (* we have 1 node as succ and the nodes are not the same (ids differ) *)
          match Node.get_pred succ with (* check that the pred of a are consistent *)
          | [] ->
             raise (Invalid_argument "Your graph is wrong")
          | [pred_node_id] when pred_node_id != (Node.get_id root) ->
             raise (Invalid_argument "Your graph is very wrong")

          | [pred_node_id] when pred_node_id = (Node.get_id root) -> (
            if List.mem (Node.get_id succ) (Node.get_pred root) then
              help_simplify keep_structure succ
            else (
              (* the only predecessor is root, we can simplify *)
              match (keep_structure, Node.get_exp root, Node.get_exp succ) with
              | (true, [], []) (* both have no exp (should never happen) *)
                | (true, [], _::_) (* root has no exp *)
                | (true, _::_, []) -> (* succ has no exp *)
                 (remove_and_recurse root succ keep_structure)
              | (true, root_exp::_, succ_exp::_) -> (
                (* no need to check every element, only the first of each node *)
                match (root_exp.node, succ_exp.node) with
                | (Skip, Skip)
                  | (Assignment(_, _), Assignment(_, _))
                  | (NonDet(_), NonDet(_))
                  | (Guard(_), Guard(_))
                  | (Allocation(_), Allocation(_))
                  | (Free(_), Free(_))
                  | (ReadHeap(_, _), ReadHeap(_, _))
                  | (WriteHeap(_, _), WriteHeap(_, _)) -> (remove_and_recurse root succ keep_structure)
                | _ -> help_simplify keep_structure succ
              )
              | (false, _, _) -> ( (* we don't need to check the exp, always simplify *)
                remove_and_recurse root succ keep_structure
              )
            )
          )
          | _ -> ( (* We have more than one predecessor, so we can't remove the
                      node succ *)
            help_simplify keep_structure succ
          )
        )
        | succs -> ( (* we have more than one succ, we cant simplify but we call
                        the function on each *)
          List.iter (help_simplify keep_structure) succs
        )
      )
    in
    help_simplify keep_structure root


  (** The module Converter provides a method [convert], that given an AST, it
      converts it into a CFG composed by nodes from the {{! Cfg.Node}Node} module.
      See {{! Cfg.CFG.make}make} to convert the resulting structure to a CFG.
      If the labeled argument keep_structure is true, only the nodes with the same
      type of HeapAtomicCommand will be in the same output Node, otherwise the exp
      list of each node could be heterogeneous. Defaults to true.
   *)
  let convert ?(keep_structure: bool = true) (root: 'a HeapRegularCommand.t) : 'a HeapAtomicCommand.t list Node.t =
    match convert_helper(root) with
    | (node, _) ->
       simplify keep_structure node;
       node
end
