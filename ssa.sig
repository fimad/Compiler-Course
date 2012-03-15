signature STATICSINGLEASSIGNMENT =
sig
  (*.*)

  val calcDF : BasicBlockGraph -> BB.BBMap
  val resolvePhi : BasicBlockGraph -> BasicBlockGraph
  val renameVariables : BasicBlockGraph -> BasicBlockGraph

  val completeSSA : BasicBlockGraph -> BasicBlockGraph

end
