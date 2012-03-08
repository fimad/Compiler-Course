signature BASICBLOCK =
sig
  (*.*)

  type BasicBlock
  type BasicBlockGraph
  structure BBMap : ORD_MAP

  val label : BasicBlock -> string
  val code : BasicBlock -> LLVM.OP list
  val succ : BasicBlockGraph -> BasicBlock -> BasicBlock list
  val pred : BasicBlockGraph -> BasicBlock -> BasicBlock list

  val def : BasicBlock -> (string*LLVM.OP) list
  val use : BasicBlock -> (string*LLVM.OP) list

  (*
  val vars_in : BasicBlockGraph -> BasicBlock -> string list
  val vars_out : BasicBlockGraph -> BasicBlock -> string list
  *)
  val in_out : BasicBlockGraph -> ((string*LLVM.OP) list BBMap.map)*((string*LLVM.OP) list BBMap.map)
  val map_lookup : (string*LLVM.OP) list BBMap.map -> BasicBlock -> (string*LLVM.OP) list
  val map_equal : (string*LLVM.OP) list BBMap.map -> (string*LLVM.OP) list BBMap.map -> bool

  val createBBGraph : LLVM.OP list -> BasicBlockGraph
  val createBBList : BasicBlockGraph -> BasicBlock list

  val toDot : string -> BasicBlockGraph -> string

  exception NoSuchBlock
  exception BadLabel

end

