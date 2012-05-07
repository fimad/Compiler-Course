
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

fun dominates dmap d n = let (* d dominates n *)
    val doms = BB.map_lookup dmap n
  in List.exists (fn x => BB.bb_equal d x) doms end

fun idom2 domMap n = let
(* It is said that a block M immediately dominates block N if M dominates N, and there is no intervening block P such that M dominates P and P dominates N. *)
  val doms = BB.map_lookup domMap n
  in case
    List.filter (fn m => 
        (List.filter (fn p => dominates domMap m p) (BB.list_diff doms [m,n])) = []
      ) (BB.list_diff doms [n])
  of
    (x::_) => x
    | _ => n
  end

fun idom bbg n = idom2 (calcDom bbg) n

fun calcDF bbg = let
    (* calculate dominator tree ? *)
    val dmap = calcDom bbg
    val dfmap = ref BB.BBMap.empty
    val dominates = dominates dmap
    val idom = idom2 dmap
    fun calcDF_help n = if not (BB.map_contains (!dfmap) n) then let (* only run this function if we haven't already been called on n *)
        val _ = (dfmap := BB.map_insert (!dfmap) n [])
        val s = ref (List.filter (fn y => not (BB.bb_equal (idom y) n)) (BB.succ bbg n)) (* compute DF_local_[n] *)
        (* A dominator tree is a tree where each node's children are those nodes it immediately dominates. Because the immediate dominator is unique, it is a tree. The start node is the root of the tree. *)
        val children = List.filter (fn c => BB.bb_equal (idom c) n) (BB.to_list bbg)
        val _ = map (fn c => let
              val _ = calcDF_help c (* compute _calcDF for all the children *)
              val wlist = BB.map_lookup (!dfmap) c
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
    val new_bbg = ref bbg
    fun def bb = map #1 (BB.def bb)

    fun var_lookup m x = (case VarMap.find (m,x) of
                SOME lst => lst
                | NONE => [])

    (*maps from variables to the nodes that 'def them*)
    val defsites = ref VarMap.empty
    (* fill up defsites yo *)
    val _ = map (fn n => map (fn v =>
            let
              val lst = var_lookup (!defsites) v
              val _ = (defsites := VarMap.insert (!defsites,v,(n::lst)))
            in
              lst
            end
          ) (def n)) (BB.to_list bbg)
    
    (*
    val _ = print "\nVARS:"
    val _ = map (fn x => print (concat ["\n",x,"\n"])) vars
    val _ = print "\nEND VARS:"
    *)

    (*place phi functions in new_bbg for variable x*)
    fun variable_phi x = let
        val inserted = ref []
        val added = ref (var_lookup (!defsites) x)
        val worklist = ref (!added)
        (*
        val _ = print (concat ["For var: ",x,"\n"])
        val _ = print (concat (map (fn b => concat ["\t",(Int.toString o BB.bb2id) b,"\n"]) (!added)))
        val _ = print (concat ["Done!\n"])
        *)
        fun step () = (case (!worklist) of
            [] => ()
          | (b::bs) => let
              val _ = (worklist := bs) (*remove b from worklist*)
              val _ = map (*for each d in the df of b*)
                (fn d => if not (BB.list_has (!inserted) d) then let
                    (*mark that we've inserted a phi function here*)
                    val _ = (inserted := d::(!inserted))
                    (*add d to the added and work list if we haven't seen it before*)
                    val _ = if not (BB.list_has (!added) d) then let
                      val _ = (added := d::(!added)) 
                      val _ = (worklist := d::(!worklist))
                      in () end else ()
                    (*actually insert a phi function*)
                    fun var v = concat ["%",v]
                    val phi = LLVM.Phi (x,(map (
                            fn p => let
                                val (bbg,label) = BB.get_label (!new_bbg) p
                                val _ = (new_bbg := bbg)
                              in
                                (LLVM.Variable x,LLVM.Variable label)
                              end
                            ) (BB.pred bbg d)))
                    val d = BB.refresh (!new_bbg) d (*make sure we have a fresh copy of d*)
                    (*val _ = (new_bbg := BB.replace (!new_bbg) (BB.set_code d ((LLVM.Phi (x,[]))::(BB.code d)))) *)
                    val _ = (new_bbg := BB.replace (!new_bbg) (BB.set_code d (LLVM.insertAfterLabel (BB.code d) [phi])))
                  in
                    ()
                  end
                 else ()
                )
                (BB.map_lookup dfmap b) (*each node in the df of b*)
            in
              step ()
            end
        )
      in
        step ()
      end
    (*actually place each phi for each var*)
    val _ = map variable_phi vars 
  in
    (!new_bbg)
  end

fun renameVariables bbg = let
  in
    bbg
  end

fun completeSSA bbg = resolvePhi bbg

end

