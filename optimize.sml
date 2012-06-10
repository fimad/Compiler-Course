(* Will Coster *)

structure Optimize :> OPTIMIZE = 
struct

structure VarMap = RedBlackMapFn (struct
  type ord_key = string
  val compare = String.compare
end)
(*
fun remove_excess_loads graph = let

    fun rm_loads m graph bb = if BB.map_contains m bb then (m,graph) else let
        val bb = BB.id2bb graph (BB.bb2id bb) (*we need to refresh our copy of the bb incase it was changed in a previous step*)

        (* takes a basic block and creats a map from which variables have been loaded (SOME res) and reset (NONE) *)
        fun load m [] = m
          | load m ((LLVM.Load (res,_,(LLVM.Variable arg)))::ode) = load (VarMap.insert (m,arg,SOME res)) ode
          | load m ((LLVM.Store (_,_,(LLVM.Variable arg)))::ode) = load (VarMap.insert (m,arg,NONE)) ode
          | load m (_::ode) = load m ode
        val load' = fn m => fn bb => load m (BB.code bb)
        val load = fn bb => load VarMap.empty (BB.code bb)

        fun pred_load bb = let
            fun pred_load' bbmap varmap bb = if BB.map_contains bbmap bb
              then (bbmap,varmap)
              else let 
                  (*val (bbmap,varmap) = foldl (fn (pbb,(bbmap,varmap)) => pred_load' (BB.map_insert bbmap bb true) varmap pbb) (bbmap,varmap) (BB.pred graph bb)*)
                  val maps = map (fn bb => pred_load' (BB.map_insert bbmap bb true) (load' varmap bb) bb) (BB.pred graph bb)
                  val (bbmap,varmap) = foldl
                    (fn ((bm',vm'),(bm,vm)) => (
                      BB.BBMap.unionWith (fn (a,b)=>a) (bm',bm) ,
                      VarMap.unionWith (fn (a,b) => if a = NONE orelse b = NONE then NONE else a) (vm',vm)
                    ))
                    (bbmap,varmap)
                    maps
                in (bbmap,varmap) end
            (*val (bbmap,varmap) = foldl (fn (bb,(bbmap,varmap)) => pred_load' bbmap varmap bb) (BB.map_insert BB.BBMap.empty bb true,VarMap.empty) (BB.pred graph bb)*)
            val (bbmap,varmap) = pred_load' (BB.map_insert BB.BBMap.empty bb true) VarMap.empty bb
          in
            varmap
          end

        val pred_loads = pred_load bb
        fun in_defs v m = (case VarMap.find (m,v) of
              NONE => NONE
            | SOME (NONE) => NONE
            | SOME (SOME v) => SOME v)
        fun filter_code to_rm new_code [] = (to_rm,new_code)
          | filter_code to_rm new_code ((c as LLVM.Load (res,ty,(LLVM.Variable var)))::rest) = (case in_defs var (VarMap.unionWith (fn (a,b) => a) ((load (BB.dummy_bb new_code)),pred_loads)) of
              NONE => filter_code to_rm (new_code@[c]) rest
            | SOME v => filter_code ((res,v)::to_rm) new_code rest)
          | filter_code to_rm new_code (c::ode) = filter_code to_rm (new_code@[c]) ode

        val (to_rm,trimmed_code) = filter_code [] [] (BB.code bb)
        (*replace any used instances of these with the appropriate variables*)
        val new_code = LLVM.replaceVar to_rm trimmed_code
        val trimmed_graph = BB.replace graph (BB.set_code bb new_code)
        val new_graph = foldl (fn (bb,g) => BB.replace g (BB.set_code bb (LLVM.replaceVar to_rm (BB.code bb)))) trimmed_graph (BB.to_list trimmed_graph)
        val new_map = BB.map_insert m bb true
      in
        (*run abail_expr for each successor of the current bb*)
        foldl (fn (bb,(m,g)) => rm_loads m g bb) (new_map,new_graph) (BB.succ new_graph bb)
      end
    val (_,new_graph) = rm_loads BB.BBMap.empty graph (BB.root graph)
  in
    new_graph
  end
*)
fun remove_excess_loads graph = graph

(*
fun available_expressions graph = let
    fun avail_expr m graph bb = if BB.map_contains m bb then (m,graph) else let
        val bb = BB.id2bb graph (BB.bb2id bb) (*we need to refresh our copy of the bb incase it was changed in a previous step*)
        val pred_defs = BB.pred_def graph bb
        (*returns optionally the variable that already contains the needed result*)
        fun in_defs c [] = NONE
          | in_defs c ((v,p)::defs) = if LLVM.eqOP c p then SOME v else in_defs c defs
        (*constructs a replace (old,new) list and removes redundant lines of code*)
        fun filter_code to_rm new_code [] = (to_rm,new_code)
                                                                   (*can't just use pred_defs, need to include all previous code in current bb aswell*)
          | filter_code to_rm new_code (c::ode) = (case (in_defs c (List.concat [(BB.def (BB.dummy_bb new_code)),pred_defs]),LLVM.resultOf c) of
              (SOME v,SOME cv) => filter_code ((cv,v)::to_rm) new_code ode
            | _ => filter_code to_rm (new_code@[c]) ode)
        (*trim out unneeded lines*)
        val (to_rm,trimmed_code) = filter_code [] [] (BB.code bb)
        (*replace any used instances of these with the appropriate variables*)
        val new_code = LLVM.replaceVar to_rm trimmed_code
        val trimmed_graph = BB.replace graph (BB.set_code bb new_code)
        val new_graph = foldl (fn (bb,g) => BB.replace g (BB.set_code bb (LLVM.replaceVar to_rm (BB.code bb)))) trimmed_graph (BB.to_list trimmed_graph)
        val new_map = BB.map_insert m bb true
      in
        (*run abail_expr for each successor of the current bb*)
        foldl (fn (bb,(m,g)) => avail_expr m g bb) (new_map,new_graph) (BB.succ new_graph bb)
      end
    val (_,new_graph) = avail_expr BB.BBMap.empty graph (BB.root graph)
  in
    (*run until no changes take place*)
    if BB.graph_equal new_graph graph then new_graph else available_expressions new_graph
  end
*)
fun available_expressions graph = graph

fun merge_bb bbg = let
    val new_bbg = ref bbg
    (* iterates through the list of basic blocks until it finds a pair it can merge, then it calls itself again from the start *)
    fun merge_help [] = ()
      | merge_help (bb::bbs) = (case BB.succ (!new_bbg) bb of
          [s] => let
              val s_code = BB.code s
              val p_code = BB.code bb
            in
              (case (p_code,s_code) of 
                ([LLVM.DefnLabel p_label,LLVM.Br _], ((LLVM.DefnLabel s_label)::_)) => let
                    val _ = (new_bbg := BB.replace (BB.replace (!new_bbg) (BB.set_code bb s_code)) (BB.set_code s []))
                    val _ = (new_bbg := BB.replace_var (!new_bbg) [(s_label,(LLVM.Variable p_label))])
                  in
                    ()
                  end
                | _ => 
                  (case BB.pred (!new_bbg) s of (*if bb has just one successor*)
                      [p] => let(*and that one successor has just one predeccsesor, MERGE 'EM!*)
                        in
                          (case (p_code,s_code) of 
                              ([],_) => merge_help bbs
                            | (_,[]) => merge_help bbs
                            | (p_code, ((LLVM.DefnLabel s_label)::_)) => let
                                val _ = (new_bbg := BB.replace (BB.replace (!new_bbg) (BB.set_code p (((rev o tl o rev) p_code)@(tl s_code)))) (BB.set_code s []))
                                val (bg,p_label) = BB.get_label (!new_bbg) p
                                val _ = (new_bbg := BB.replace_var bg [(s_label,(LLVM.Variable p_label))])
                              in
                                ()
                              end
                            | (p_code,s_code) => (new_bbg := BB.replace (BB.replace (!new_bbg) (BB.set_code p (p_code@s_code))) (BB.set_code s [])))
                        end
                     | _  => merge_help bbs)
              )
              end
            | _   => merge_help bbs
        )

    (*call merge_help *)
    val _ = merge_help (BB.to_list bbg)
  in
    (!new_bbg)
  end

fun tailcall bbg = let
      fun insertTailCalls [] = []
        | insertTailCalls ((LLVM.Ret r)::(LLVM.Call c)::cs) = (LLVM.Ret r)::(insertTailCalls ((LLVM.TailCall c)::cs))
        | insertTailCalls ((LLVM.TailCall t)::(LLVM.Call c)::cs) = (LLVM.TailCall t)::(insertTailCalls ((LLVM.TailCall c)::cs))
        | insertTailCalls ((LLVM.TailPrint t)::(LLVM.Call c)::cs) = (LLVM.TailPrint t)::(insertTailCalls ((LLVM.TailCall c)::cs))
        | insertTailCalls ((LLVM.Ret r)::(LLVM.Print c)::cs) = (LLVM.Ret r)::(insertTailCalls ((LLVM.TailPrint c)::cs))
        | insertTailCalls ((LLVM.TailCall t)::(LLVM.Print c)::cs) = (LLVM.TailCall t)::(insertTailCalls ((LLVM.TailPrint c)::cs))
        | insertTailCalls ((LLVM.TailPrint t)::(LLVM.Print c)::cs) = (LLVM.TailPrint t)::(insertTailCalls ((LLVM.TailPrint c)::cs))
        | insertTailCalls (c::cs) = c::(insertTailCalls cs)
  in
    (* foldl (fn (bb,bbg) => BB.replace bbg (BB.set_code bb ((insertTailCalls o BB.code) bb))) bbg (BB.to_list bbg)*)
    BB.createBBGraph ((rev o insertTailCalls o rev o BB.graph2code) bbg)
  end

val max_level = 1
fun optimize i graph = (case i of
    (*
        1 => optimize (i-1) (remove_excess_loads graph)
      | 2 => optimize (i-1) (available_expressions graph)
    *)
        1 => optimize (i-1) (tailcall graph)
      | 2 => optimize (i-1) (merge_bb graph)
      | _ => graph)

end
