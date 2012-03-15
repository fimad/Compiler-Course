
structure SSA :> STATICSINGLEASSIGNMENT = 
struct

(*
  // dominator of the start node is the start itself
  Dom(n0) = {n0}
   // for all other nodes, set all nodes as the dominators
   for each n in N - {n0}
        Dom(n) = N;
         // iteratively eliminate nodes that are not dominators
         while changes in any Dom(n)
              for each n in N - {n0}:
                       Dom(n) = {n} union with intersection over all p in pred(n) of Dom(p)
*)
fun calcDom bbg = let
    val dmap = ref BB.BBMap.empty
    val root = BB.root bbg
    dmap := BB.map_insert !dmap root [root]
    fun _calcDom old_dmap = let
        val _ = map (fn n => dmap := BB.map_insert !dmap (
              foldl (fn (p,b) => BB.list_union b (let SOME d = BB.map_find !dmap p in d end)) [n] (BB.pred n)
            )) (BB.list_diff (BB.to_list bbg) [root])
      in
        if BB.map_equal old_dmap !dmap then !dmap else _calcDom !dmap
      end
  in
    _calcDom !dmap
  end

fun calcDF bbg = let
    (* calculate dominator tree ? *)
    val dmap = calcDom bbg
    val dfmap = ref BB.BBMap.empty
    fun dominates d n = let
        val SOME doms = BB.map_find dmap n
      in (List.filter (fn x => BB.bb_equal n x) doms) <> [] end
    fun idom n = let
    (* It is said that a block M immediately dominates block N if M dominates N, and there is no intervening block P such that M dominates P and P dominates N. *)
      val SOME doms = BB.map_find dmap n
      val (x::_) = filter (fn m => 
            (filter (fn p => (dominates m p) andalso (dominates p n)) (BB.list_diff doms [m])) = []
          ) doms
      in x end
    fun _calcDF n = if not (BB.map_contains !dfmap n) then let (* only run this function if we haven't already been called on n *)
        dfmap := BB.map_insert !dfmap n []
        val s = ref filter (fn y => idom y <> n) (succ n) (* compute DF_local_[n] *)
        val children = filter (fn c => not (BB.map_contains !dfmap c)) (succ n)
        val _ = map (fn c => let
              val = _calcDF c (* compute _calcDF for all the children *)
              val SOME wlist = BB.map_find !dfmap c
              s := BB.list_union !s (filter (fn w => not (dominates n w) orelse BB.bb_equal n w) wlist)
            in () end
          ) children
        dfmap := BB.map_insert !dfmap n s
      in
        ()
      end else ()
    val _ = _calcDF (BB.root bbg)
  in
    !dfmap
  end

fun resolvePhi bbg = let
    structure VarMap = RedBlackMapFn (struct
        type ord_key = string
        val compare = String.compare
      end)
    structure PhiMap = RedBlackMapFn (struct
        type ord_key = (string,BB.BasicBlock)
        val compare = (fn ((s1,b1),(s2,b2)) => let
            val scmp = String.compare (s1,s2)
            val bcmp = BB.bb_compare (b1,b2)
          in
            if scmp = EQUAL then bcmp else scmp
          end)
      end)
    val dfmap = calcDF bbg
    val vars = BB.variables bbg
    fun real_def bb = map BB.isRealVariable (BB.def bb)
    val defsites = ref VarMap.empty
    val _ = map (fn n => map (fn v =>
            let
              val lst = (case VarMap.find (!defsites,v) of
                SOME lst => lst
                | NONE => [])
              defsites := VarMap.insert (!defsites,v,(n::lst))
            in
              ()
            end
          ) (real_def n)) [] (BB.to_list bbg)
    val new_bbg = ref bbg
    val phisites = ref PhiMap.empty
    fun forvar a [] = ()
      | forvar a (n::w) = let
          val SOME df_n = BB.map_find dfmap n
        in
          forvar a (w@(List.concat(
            map (fn y => 
                if PhiMap.find (!phisites,(a,y)) <> NONE then
                  let
                    new_bbg := BB.replace !new_bbg (BB.set_code y ((LLVM.Phi (a,[]))::(BB.code y)))
                    phisites := PhiMap.insert (!phisites,(a,y),true)
                  in
                    if (List.find (fn x => x=a) (real_def y)) <> [] then [y] else []
                  end
                else []
            ) df_n
          )))
        end
    val _ = map (fn v => let val SOME w = VarMap.find (!defsites,v) in forvar v w end) vars
  in
    !new_bbg
    (* TODO add actual parameters to the phi functions, right now they are bare as fuck *)
  end

fun renameVariables bbg = let
  in
    bbg
  end

fun completeSSA bbg = renameVariables (resolvePhi bbg)

end

