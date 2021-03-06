signature BASICBLOCK =
sig
  (*.*)

  type BasicBlock
  type Annotation
  type BasicBlockGraph
  structure BBMap : ORD_MAP
  structure BBSet : ORD_SET where type item = BasicBlock

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
  val to_set : BasicBlockGraph -> BBSet.set
  val to_graph : BasicBlockGraph -> Graph.graph
  val root : BasicBlockGraph -> BasicBlock
  val refresh : BasicBlockGraph -> BasicBlock -> BasicBlock
  val id2bb : BasicBlockGraph -> int -> BasicBlock
  val bb2id : BasicBlock -> int
  val graph2code : BasicBlockGraph -> LLVM.OP list
  val num_blocks : BasicBlockGraph -> int
  val bb_equal : BasicBlock -> BasicBlock -> bool
  val bb_eq : (BasicBlock * BasicBlock) -> bool
  val bb_compare : (BasicBlock * BasicBlock) -> order

  val replace_var : BasicBlockGraph -> (LLVM.Arg*LLVM.Arg) list -> BasicBlockGraph

  val variables : BasicBlockGraph -> string list
  val isRealVariable : string -> bool (* is it a proper variable or a temp? *)

  val def : BasicBlock -> (string*LLVM.OP) list
  val use : BasicBlock -> (string*LLVM.OP) list

  (*
  val pred_def : BasicBlockGraph -> BasicBlock -> (string*LLVM.OP) list
  *)

  val dummy_bb : LLVM.OP list -> BasicBlock

  val in_out : BasicBlockGraph -> ((string*LLVM.OP) list BBMap.map)*((string*LLVM.OP) list BBMap.map)

  (*
  val list_uniqify' : (('a * 'a) -> bool) -> 'a list -> 'a list
  val list_union' : (('a * 'a) -> bool) -> 'a list -> 'a list -> 'a list
  val list_inter' : (('a * 'a) -> bool) -> 'a list -> 'a list -> 'a list
  val list_diff' : (('a * 'a) -> bool) -> 'a list -> 'a list -> 'a list
  val list_equal' : (('a * 'a) -> bool) -> 'a list -> 'a list -> bool
  val list_has' : (('a * 'a) -> bool) -> 'a list -> 'a -> bool

  val list_uniqify : ''a list -> ''a list
  val list_union : ''a list -> ''a list -> ''a list
  val list_inter : ''a list -> ''a list -> ''a list
  val list_diff : ''a list -> ''a list -> ''a list
  val list_equal : ''a list -> ''a list -> bool
  val list_has : ''a list -> ''a -> bool
  *)

  val map_equal' : (('a * 'a) -> bool) -> 'a BBMap.map -> 'a BBMap.map -> bool

  val map_lookup : 'a list BBMap.map -> BasicBlock -> 'a list
  val map_lookup_set : BBSet.set BBMap.map -> BasicBlock -> BBSet.set
  val map_equal : ''a BBMap.map -> ''a BBMap.map -> bool
  val map_contains : 'a BBMap.map -> BasicBlock -> bool
  val map_insert : 'a BBMap.map -> BasicBlock -> 'a -> 'a BBMap.map
  val map_find : 'a BBMap.map -> BasicBlock -> 'a option

  val graph_equal : BasicBlockGraph -> BasicBlockGraph -> bool

  val createBBGraph : LLVM.OP list -> BasicBlockGraph

  exception NoSuchBlock
  exception BadLabel

end

