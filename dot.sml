
structure DOT :> DOTS = 
struct
  
  (**********************************
   *              TODOT             *
   **********************************)

  fun toDot title bbgraph annotated = let
      val (bbin,bbout) = BB.in_out bbgraph
      val doms = SSA.calcDom bbgraph
      val df = SSA.calcDF bbgraph 
      fun fixendl [] = []
        | fixendl (c::cs) = if (str c) = "\n" then (explode "\\n")@(fixendl cs) else c::(fixendl cs)
      fun combine glue lst = foldr (fn (a,b) => concat [a,glue,b]) "" lst
      fun stripcode [] = []
        | stripcode ((s,code)::xs) = s::(stripcode xs)
      fun definitions [] = []
        | definitions (bb::rest) = (concat ([
            "\tBB", Int.toString(BB.bb2id bb)," [label=\"",
              (implode (fixendl (explode (combine "\\n" (map LLVM.printOP (BB.code bb))))))
              ]@(if annotated then
                ["\\n----------------",
                "\\n\\nid: ",(combine ", " [Int.toString (BB.bb2id bb)]),
                "\\n\\nuse: ",(combine ", " (stripcode (BB.use bb))),
                "\\ndef: ",(combine ", " (stripcode (BB.def bb))),
                "\\n\\nin: ",(combine ", " (stripcode (BB.map_lookup bbin bb))),
                "\\nout: ",(combine ", " (stripcode (BB.map_lookup bbout bb))),
                "\\n\\nsucc: ",(combine ", " (map (Int.toString o BB.bb2id) (BB.succ bbgraph bb))),
                "\\npred: ",(combine ", " (map (Int.toString o BB.bb2id) (BB.pred bbgraph bb))),
                "\\n\\nidom: ",(combine ", " (map (Int.toString o BB.bb2id) [SSA.idom bbgraph bb])),
                "\\n\\ndominators: ",(combine ", " (map (Int.toString o BB.bb2id) (BB.map_lookup doms bb))),
                "\\ndominance frontier: ",(combine ", " (map (Int.toString o BB.bb2id) (BB.map_lookup df bb)))]
              else
                [""])@[
              "\"];\n",
            "\tBB", Int.toString(BB.bb2id bb)," [shape=box];" ]))::(definitions rest)
      fun edges [] = []
        | edges (bb::rest) = (combine "\n" (map (fn i => (concat [
            "\tBB", Int.toString(BB.bb2id bb)," -> BB",Int.toString(Graph.toInt i),";" ])) (Graph.succ (Graph.toNode((BB.to_graph bbgraph),BB.bb2id bb)))))::(edges rest)
    in
      concat [
          "digraph ",title," {\n"
        , (combine "\n" (definitions (BB.to_list bbgraph)))
        , (combine "\n" (edges (BB.to_list bbgraph)))
        , "\n}\n" ]
    end


end

