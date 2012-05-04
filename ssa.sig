signature STATICSINGLEASSIGNMENT =
sig
  (*.*)

  val calcDom : BB.BasicBlockGraph -> (BB.BasicBlock list) BB.BBMap.map
  val calcDF : BB.BasicBlockGraph -> (BB.BasicBlock list) BB.BBMap.map
  val resolvePhi : BB.BasicBlockGraph -> BB.BasicBlockGraph
  val renameVariables : BB.BasicBlockGraph -> BB.BasicBlockGraph

  val completeSSA : BB.BasicBlockGraph -> BB.BasicBlockGraph

end
