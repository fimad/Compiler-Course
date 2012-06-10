
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
    val all_but_root = BB.list_diff' BB.bb_eq (BB.to_list bbg) [root]
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
              foldl (fn (p,b) => BB.list_inter' BB.bb_eq  b (let val d = BB.map_lookup (!dmap) p in d end)) (BB.to_list bbg) (BB.pred bbg n)
            ))) (BB.list_diff' BB.bb_eq (BB.to_list bbg) [root]) (* for each n in N-{n0} *)
      in
        (* while changes in any Dom(n) *)
        if BB.map_equal' BB.bb_eq old_dmap (!dmap) then (!dmap) else calcDom_help (!dmap)
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
        length (List.filter (fn p => dominates domMap m p) (BB.list_diff' BB.bb_eq doms [m,n])) = 0
      ) (BB.list_diff' BB.bb_eq doms [n])
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
              val _ = (s := BB.list_union' BB.bb_eq (!s) (List.filter (fn w => not (dominates n w) orelse BB.bb_equal n w) wlist))
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

    val (in_map,out_map) = BB.in_out bbg
    (* if more than one predecessor of b has x as an out variable *)
    (* and x is used in b *)
    fun b_needs_phi_for_x b x = let
        val l = length (List.filter (
              fn p => List.exists (fn (v,_) => v = x) (BB.map_lookup out_map p)
            ) (BB.pred bbg b))
        (*val _ = print (concat ["var: ",x," , bb:",(Int.toString (BB.bb2id b)),", length: ",(Int.toString l),"\n"])*)
      in l > 1(* andalso List.exists (fn y => y=x) (map (#1) (BB.use b))*)
      end

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
                (fn d => if (not (BB.list_has' BB.bb_eq (!inserted) d) andalso b_needs_phi_for_x d x) then let
                    (*mark that we've inserted a phi function here*)
                    val _ = (inserted := d::(!inserted))
                    (*add d to the added and work list if we haven't seen it before*)
                    val _ = if not (BB.list_has' BB.bb_eq (!added) d) then let
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
    (* calculate dominator tree ? *)
    val dmap = calcDom bbg
    val dfmap = calcDF bbg
    val vars = BB.variables bbg
    val new_bbg = ref bbg

    fun linear_map f [] = []
      | linear_map f (x::xs) = (f x)::(linear_map f xs)

    fun rename_var x = let
        val next_x_sub = ref 0;
        fun next_x () = let
          val _ = (next_x_sub := (!next_x_sub) + 1) (*increment the subscript*)
          val var = (concat [x,"__",(Int.toString (!next_x_sub))])
          in var end
        fun current_x () = let
          val var = (concat [x,"__",(Int.toString (!next_x_sub))])
          in var end

        fun rename_bb bb last_x =
          let
            (* val _ = print (concat ["Working on: ",x," in: ",(Int.toString (BB.bb2id bb)),"\n"]) *)
            val bb = BB.refresh (!new_bbg) bb (*make sure we have a fresh copy of bb*)
            val my_last_x = ref last_x
            val new_code = linear_map ( (* performs the equivalent of the first for loop in the sample code *)
                  fn line => let
                      (* save the current_x so that setting the result doesn't accidently update current_x before the arg can look at it *)
                      val current_x = (!my_last_x)
                      fun change_result r = if r = x then
                          let 
                            val _ = (my_last_x := next_x ())
                          in (!my_last_x) end
                        else r
                      fun change_arg (LLVM.Variable v) = if v = x then (LLVM.Variable current_x) else (LLVM.Variable v)
                        | change_arg a = a
                    in
                      case line of
                          (LLVM.Load (r,t,a1)) => LLVM.Load ((change_result r),t,(change_arg a1))
                        | (LLVM.GetElementPtr (r,t,a1,a2)) => LLVM.GetElementPtr ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Store (t,a1,a2)) => LLVM.Store (t,(change_arg a1),(change_arg a2))
                        | (LLVM.Add (r,t,a1,a2)) => LLVM.Add ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Sub (r,t,a1,a2)) => LLVM.Sub ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Mul (r,t,a1,a2)) => LLVM.Mul ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Div (r,t,a1,a2)) => LLVM.Div ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpEq (r,t,a1,a2)) => LLVM.CmpEq ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpNe (r,t,a1,a2)) => LLVM.CmpNe ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpGt (r,t,a1,a2)) => LLVM.CmpGt ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpGe (r,t,a1,a2)) => LLVM.CmpGe ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpLt (r,t,a1,a2)) => LLVM.CmpLt ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CmpLe (r,t,a1,a2)) => LLVM.CmpLe ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.CndBr (a1,a2,a3)) => LLVM.CndBr ((change_arg a1),(change_arg a2),(change_arg a3))
                        | (LLVM.Ret (t,a1)) => LLVM.Ret (t,(change_arg a1))
                        | (LLVM.And (r,t,a1,a2)) => LLVM.And ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Or (r,t,a1,a2)) => LLVM.Or ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Alloca (r,t,i)) => LLVM.Alloca ((change_result r),t,i)
                        | (LLVM.Ashr (r,t,a1,a2)) => LLVM.Ashr ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Xor (r,t,a1,a2)) => LLVM.Xor ((change_result r),t,(change_arg a1),(change_arg a2))
                        | (LLVM.Call (r,t,func,args)) => LLVM.Call ((change_result r),t,func,(map (fn (r,t) => (change_arg r,t)) args))
                        | (LLVM.Print (r,t,arg)) => LLVM.Print ((change_result r),t,(change_arg arg))
                        | (LLVM.Phi (r,args)) => LLVM.Phi ((change_result r), args)
                        | (LLVM.ZExt (r,t1,a1,t2)) => LLVM.ZExt ((change_result r),t1,(change_arg a1),t2)
                        | (LLVM.SiToFp (r,t1,a1,t2)) => LLVM.SiToFp ((change_result r),t1,(change_arg a1),t2)
                        | (LLVM.Bitcast (r,t1,a1,t2)) => LLVM.Bitcast ((change_result r),t1,(change_arg a1),t2)
                        | (LLVM.Alias ((LLVM.Variable r),a)) => LLVM.Alias (LLVM.Variable (change_result r), (change_arg a))
                        | x => x (* default: don't change anything *)
                    end
                ) (BB.code bb)
            (* set bb's code to new_code *)
            val _ = (new_bbg := BB.replace (!new_bbg) (BB.set_code bb new_code))

            (*set the content of each of the successor's phi instructions*)
            val _ = linear_map (fn s => let
                  val s = BB.refresh (!new_bbg) s
                  val (_,my_label) = BB.get_label (!new_bbg) bb
                  val new_code = map (
                      fn (LLVM.Phi (r,args)) =>
                          LLVM.Phi (r,(map (fn (v as LLVM.Variable v_str,(l as LLVM.Variable l_str)) => ((if x = v_str andalso my_label = l_str then LLVM.Variable (!my_last_x) else v),l)) args))
                       | x => x
                    ) (BB.code s)
                  val _ = (new_bbg := BB.replace (!new_bbg) (BB.set_code s new_code))
                  in () end
                ) (BB.succ (!new_bbg) bb)

            (* recurse down the dominator tree *)
            val children = List.filter (fn c => (BB.bb_equal (idom (!new_bbg) c) bb) andalso not (BB.bb_equal bb c)) (BB.to_list (!new_bbg))
            val _ = map (fn c => rename_bb c (!my_last_x)) (children)
          in
            ()
          end
      in
        rename_bb (BB.root (!new_bbg)) (current_x ())
      end

    (* rename each variable *)
    val _ = linear_map rename_var vars
  in
    (!new_bbg)
  end


fun removeAliases bbg = let
    fun find_aliases [] = []
      | find_aliases ((LLVM.Alias ((LLVM.Variable a),value))::xs) = (a,value)::(find_aliases xs)
      | find_aliases (_::xs) = find_aliases xs
    val aliases = List.concat (map (find_aliases o BB.code) (BB.to_list bbg))

    (* remove all alias op codes from a code list *)
    fun rmAliasOps [] = []
      | rmAliasOps ((LLVM.Alias _)::xs) = rmAliasOps xs
      | rmAliasOps (x::xs) = x::(rmAliasOps xs)
  in
    foldl (fn (bb,bbg) => BB.replace bbg (BB.set_code bb (((map (LLVM.replaceInOp aliases)) o rmAliasOps o BB.code) bb))) bbg (BB.to_list bbg)
    (* bbg *)
  end

(* Well fuck, llvm checks this... *)
(*
fun fixPhis bbg = let
    (* it happens occaisonaly in programs with bugs, that an arg will reference an undefined variable %_#__0, get rid of these so it still compiles *)
    fun stripBadArgs [] = []
      | stripBadArgs ((arg as (LLVM.Variable arg_str,_))::args) = let
          (*val _ = print (concat ["HEY: ",arg_str,"\n"])*)
        in
          (case (String.explode arg_str,(rev o String.explode) arg_str) of
            (((#"_")::_),((#"0")::(#"_")::(#"_")::_)) => stripBadArgs args (*this is a bad arg, get rid of it!*)
            | _ => arg::(stripBadArgs args))
        end
    fun fixPhisInCode code =
      map (
        fn (LLVM.Phi (r,args)) => LLVM.Phi (r,stripBadArgs args) | x => x
      ) code
  in
    foldl (fn (bb,bbg) => BB.replace bbg (BB.set_code bb (fixPhisInCode (BB.code bb)) )) bbg (BB.to_list bbg)
  end
*)
    
fun completeSSA bbg = (removeAliases o renameVariables o resolvePhi) bbg

end

