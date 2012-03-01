signature BASICBLOCK =
sig

  type BasicBlock
  type BasicBlockGraph

  val label : BasicBlock -> string
  val code : BasicBlock -> LLVM.OP list
  val succ : BasicBlockGraph -> BasicBlock -> BasicBlock list
  val pred : BasicBlockGraph -> BasicBlock -> BasicBlock list

  val def : BasicBlock -> string list
  val use : BasicBlock -> string list

  val createBBGraph : LLVM.OP list -> BasicBlockGraph
  val createBBList : BasicBlockGraph -> BasicBlock list

  val toDot : string -> BasicBlockGraph -> string

  exception NoSuchBlock

end

