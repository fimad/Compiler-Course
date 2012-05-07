signature BASICBLOCK =
sig
  (*.*)

  eqtype BasicBlock
  type Annotation
  type BasicBlockGraph
  structure BBMap : ORD_MAP

  val label2int : Annotation -> int

  val label : BasicBlock -> string
  val code : BasicBlock -> LLVM.OP list
  val set_code : BasicBlock -> LLVM.OP list -> BasicBlock
  val succ : BasicBlockGraph -> BasicBlock -> BasicBlock list
  val pred : BasicBlockGraph -> BasicBlock -> BasicBlock list

  val get_label : BasicBlockGraph -> BasicBlock -> (BasicBlockGraph*string) (*will add a label if need be, so it might change the graph*)
  val block_map : BasicBlockGraph -> (BasicBlock -> BasicBlock) -> BasicBlockGraph
  val code_map : BasicBlockGraph -> (LLVM.OP -> LLVM.OP) -> BasicBlockGraph
  val replace : BasicBlockGraph -> BasicBlock -> BasicBlockGraph
  val to_list : BasicBlockGraph -> BasicBlock list
  val to_graph : BasicBlockGraph -> Graph.graph
  val root : BasicBlockGraph -> BasicBlock
  val refresh : BasicBlockGraph -> BasicBlock -> BasicBlock
  val id2bb : BasicBlockGraph -> int -> BasicBlock
  val bb2id : BasicBlock -> int
  val graph2code : BasicBlockGraph -> LLVM.OP list
  val num_blocks : BasicBlockGraph -> int
  val bb_equal : BasicBlock -> BasicBlock -> bool
  val bb_compare : (BasicBlock * BasicBlock) -> order

  val variables : BasicBlockGraph -> string list
  val isRealVariable : string -> bool (* is it a proper variable or a temp? *)

  val def : BasicBlock -> (string*LLVM.OP) list
  val use : BasicBlock -> (string*LLVM.OP) list

  val pred_def : BasicBlockGraph -> BasicBlock -> (string*LLVM.OP) list

  val dummy_bb : LLVM.OP list -> BasicBlock

  val in_out : BasicBlockGraph -> ((string*LLVM.OP) list BBMap.map)*((string*LLVM.OP) list BBMap.map)

  val list_uniqify : ''a list -> ''a list
  val list_union : ''a list -> ''a list -> ''a list
  val list_inter : ''a list -> ''a list -> ''a list
  val list_diff : ''a list -> ''a list -> ''a list
  val list_equal : ''a list -> ''a list -> bool
  val list_has : ''a list -> ''a -> bool

  val map_lookup : ''a list BBMap.map -> BasicBlock -> ''a list
  val map_equal : ''a list BBMap.map -> ''a list BBMap.map -> bool
  val map_contains : ''a BBMap.map -> BasicBlock -> bool
  val map_insert : ''a BBMap.map -> BasicBlock -> ''a -> ''a BBMap.map
  val map_find : ''a BBMap.map -> BasicBlock -> ''a option

  val graph_equal : BasicBlockGraph -> BasicBlockGraph -> bool

  val createBBGraph : LLVM.OP list -> BasicBlockGraph
  val createBBList : BasicBlockGraph -> BasicBlock list

  exception NoSuchBlock
  exception BadLabel

end

