include Analysis_DataStructures_Base

(** Parser related data structures *)
module Parser = struct
  module LogicFormulas = LogicFormulas
  module Commands = RegularCommands
end

(** Analysis related data structures *)
module Analysis = struct
  include ControlFlowGraph
  include State
end