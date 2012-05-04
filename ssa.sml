
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
    val all_but_root = BB.list_diff (BB.to_list bbg) [root]
    (*  Dom(n0) = {n0} *)
    val _ = let in dmap := (BB.map_insert (!dmap) root [root]) end
    (*
       for each n in N - {n0}
          Dom(n) = N;
    *)
    val _ = let in dmap := (foldl (fn (bb,m)=>BB.map_insert m bb (BB.to_list bbg)) (!dmap) all_but_root) end
    (*
       while changes in any Dom(n)
            for each n in N - {n0}:
                     Dom(n) = {n} union with intersection over all p in pred(n) of Dom(p)
    *)
    fun calcDom_help old_dmap = let
        val _ = map (fn n => dmap := BB.map_insert (!dmap) n (n::(
               (* Dom(n) = {n} union with intersection over all p in pred(n) of Dom(p) *)
              foldl (fn (p,b) => BB.list_inter b (let val d = BB.map_lookup (!dmap) p in d end)) (BB.to_list bbg) (BB.pred bbg n)
            ))) (BB.list_diff (BB.to_list bbg) [root]) (* for each n in N-{n0} *)
      in
        (* while changes in any Dom(n) *)
        if BB.map_equal old_dmap (!dmap) then (!dmap) else calcDom_help (!dmap)
      end
  in
    calcDom_help (!dmap)
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
      val (x::_) = List.filter (fn m => 
            (List.filter (fn p => (dominates m p) andalso (dominates p n)) (BB.list_diff doms [m])) = []
          ) doms
      in x end
    fun calcDF_help n = if not (BB.map_contains (!dfmap) n) then let (* only run this function if we haven't already been called on n *)
        val _ = (dfmap := BB.map_insert (!dfmap) n [])
        val s = ref (List.filter (fn y => idom y <> n) (BB.succ bbg n)) (* compute DF_local_[n] *)
        val children = List.filter (fn c => not (BB.map_contains (!dfmap) c)) (BB.succ bbg n)
        val _ = map (fn c => let
              val _ = calcDF_help c (* compute _calcDF for all the children *)
              val SOME wlist = BB.map_find (!dfmap) c
              val _ = (s := BB.list_union (!s) (List.filter (fn w => not (dominates n w) orelse BB.bb_equal n w) wlist))
            in () end) children
        val _ = (dfmap := BB.map_insert (!dfmap) n (!s))
      in
        ()
      end else ()
    val _ = calcDF_help (BB.root bbg)
  in
    !dfmap
  end

structure VarMap = RedBlackMapFn (struct
    type ord_key = string
    val compare = String.compare
  end)
structure PhiMap = RedBlackMapFn (struct
    type ord_key = string*BB.BasicBlock
    val compare = (fn ((s1,b1),(s2,b2)) => let
        val scmp = String.compare (s1,s2)
        val bcmp = BB.bb_compare (b1,b2)
      in
        if scmp = EQUAL then bcmp else scmp
      end)
  end)
fun resolvePhi bbg = let
    val dfmap = calcDF bbg
    val vars = BB.variables bbg
    fun real_def bb = List.filter BB.isRealVariable (map #1 (BB.def bb))
    val defsites = ref VarMap.empty
    (* fill up defsites yo *)
    val _ = map (fn n => map (fn v =>
            let
              val lst = (case VarMap.find (!defsites,v) of
                SOME lst => lst
                | NONE => [])
              val _ = (defsites := VarMap.insert (!defsites,v,(n::lst)))
            in
              lst
            end
          ) (real_def n)) (BB.to_list bbg)
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
                    val _ = (new_bbg := BB.replace (!new_bbg) (BB.set_code y ((LLVM.Phi (a,[]))::(BB.code y))))
                    val _ = (phisites := PhiMap.insert (!phisites,(a,y),true))
                  in
                    if (List.filter (fn x => x=a) (real_def y)) <> [] then [y] else []
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

