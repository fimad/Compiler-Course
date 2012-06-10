(* Will Coster *)

structure BB :> BASICBLOCK = 
struct
  

(*Internal datatypes*)
  datatype Annotation =
      Label of string*int
    | NoLabel of int
  fun label2int (Label (_,i)) = i
    | label2int (NoLabel i) = i
(*Internal Basic blocks are lists of op codes *)
  type BasicBlock' = LLVM.OP list
  type BasicBlock = Annotation*BasicBlock'
  type BasicBlockGraph = Graph.graph*(BasicBlock list)

  
  (**********************************
   * LIST AND MAP UTILITY FUNCTIONS *
   **********************************)

  (* functions for treating lists like sets *)
  (* for each element in xs, filter the remaining list *)
  (* non order preserving *)
  fun list_has lst a = List.exists (fn b => a=b) lst
  fun list_has' e lst a = List.exists (fn b => e (a,b)) lst

  fun list_uniqify xs = foldl (fn (x,xs) => x::(List.filter (fn y => x<>y) xs) ) xs xs
  fun list_uniqify' e xs = foldl (fn (x,xs) => x::(List.filter (fn y => not (e (x,y))) xs) ) xs xs

  (*subtracts the contents of list b from list a*)
  fun list_diff equals a [] = a
    | list_diff equals a (b::bs) = list_diff equals (List.filter (fn x => not (equals (b,x))) a) bs
  fun list_diff' e a b = list_uniqify' e (list_diff e a b)
  val list_diff = (fn a => fn b => list_uniqify (list_diff (op =) a b))

  fun list_union a b = list_uniqify (a@b)
  fun list_union' e a b = list_uniqify' e (a@b)

  fun list_inter' e a [] = []
    | list_inter' e a (b::bs) = (if list_has' e a b then [b] else [])@(list_inter' e a bs)
  fun list_inter a b = list_inter' (op =) a b

  (*returns true if two lists are set-wise equal*)
  fun list_equal' e [] [] = true
    | list_equal' e [] _ = false
    | list_equal' e _ [] = false
    | list_equal' e (x::xs) ys = let
      fun rm ls = List.filter (fn z => not (e (z,x))) ls
      in list_equal' e (rm xs) (rm ys) end
  fun list_equal a b = list_equal' (op =) a b

  (*functions for dealing with maps of basic blocks to lists*)
  val bb_compare = (fn ((xl,_),(yl,_)) => Int.compare( label2int xl, label2int yl))
  structure BBMap = RedBlackMapFn (struct
      type ord_key = BasicBlock
      val compare = bb_compare
    end)
  fun map_lookup m key = (case BBMap.find (m,key) of
        NONE => []
      | SOME v => v)
  fun map_equal' e m1 m2 = let
    fun oneway e m1 m2 = BBMap.foldli (fn (k,v,b) => if list_equal' e (map_lookup m2 k) v then b else false) true m1
    in oneway e m1 m2 andalso oneway e m2 m1 end
  fun map_equal a b = map_equal' (op =) a b
  fun map_contains m bb = if not (Option.isSome (BBMap.find (m,bb))) then false else true
  fun map_insert m bb v = BBMap.insert (m,bb,v)
  fun map_find m key = BBMap.find (m,key)

  fun graph_equal (_,bbs_1) (_,bbs_2) = list_equal' (fn (a,b) => bb_compare (a,b) = EQUAL) bbs_1 bbs_2

  
  (**********************************
   *  BASIC BLOCK UTILITY FUNCTIONS *
   **********************************)

(* functions for getting relevant info out of a basic block *)
  exception NoSuchBlock
  fun id2bb (graph,[]) id = raise NoSuchBlock
    | id2bb (graph,((label,bb)::bs)) id = if label2int label = id then (label,bb) else id2bb (graph,bs) id
  fun bb2id (label,code) = label2int label

  (*grabs a fresh copy of the bb from the graph*)
  fun refresh bbg bb = id2bb bbg (bb2id bb)

  fun code (_,code) = code
  fun set_code (label,_) code = (label,code)
  fun label (label,_) = concat ["BB",Int.toString(label2int label)]
  fun succ (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.succ (Graph.toNode (graph,label2int label)))
  fun pred (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.pred (Graph.toNode (graph,label2int label)))

  fun bb_equal (l1,_) (l2,_) = label2int l1 = label2int l2
  fun bb_eq ((l1,_),(l2,_)) = label2int l1 = label2int l2

  fun to_list (graph,bbs) = bbs
  fun to_graph (graph,bbs) = graph

  fun replace (graph,bbs) bbnew = let
      fun equals (a,_) (b,_) = a = b
    (* in (graph,bbnew::(list_diff' equals bbs [bbnew])) end *)
    in (graph,bbnew::(List.filter (not o (equals bbnew)) bbs)) end

  fun block_map (graph,bbs) f = (graph,(map f bbs))

  fun code_map (graph,bbs) f = (graph,(map (fn (label,code) => (label,map f code)) bbs))

  fun root graph = id2bb graph 0

  fun dummy_bb code = (NoLabel ~1,code)

  fun num_blocks (graph,bbs) = length bbs
  
  fun graph2code graph = let
      fun helper id = if id < (num_blocks graph) then (code (id2bb graph id))@(helper (id+1)) else []
    in helper 0 end

  fun get_label bbg bb = let
      val bb = refresh bbg bb
    in
      case (code bb) of
        ((LLVM.DefnLabel l)::rest) => (bbg, l)
      | code => let
          val label_string = LLVM_Translate.makenextlabel ()
          val label_code = LLVM.DefnLabel label_string
          val new_code = label_code::code
          val new_bbg = foldl (fn (p as (_,code),new_bbg)=>replace new_bbg (set_code p (code@[LLVM.Br (LLVM.Label label_string)]))) bbg (pred bbg bb)
        in
          (replace new_bbg (set_code bb new_code), label_string)
        end
     end

   fun replace_var bbg aliases = foldl (fn (bb,bbg) => replace bbg (set_code bb (((map (LLVM.replaceInOp aliases)) o code) bb))) bbg (to_list bbg)
  
  (**********************************
   *          DEF AND USE           *
   **********************************)
  
  fun def bb = let
      fun op2def (code as (LLVM.Load (s,_,_))) = [(s,code)]
        | op2def (code as (LLVM.GetElementPtr (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Add (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Sub (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Mul (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Div (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpEq (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpNe (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpGt (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpGe (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpLt (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.CmpLe (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.And (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Or (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Alloca (s,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Ashr (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Xor (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Call (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.TailCall (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Phi (s,_))) =  [(s,code)]
        | op2def (code as (LLVM.Print (s,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.TailPrint (s,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Alias ((LLVM.Variable s),_))) =  [(s,code)]
        | op2def (code as (LLVM.ZExt (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.SiToFp (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Bitcast (s,_,_,_))) =  [(s,code)]
        | op2def _ = []
    in
      List.concat (map op2def (code bb))
    end

    (*
  fun pred_def graph bb = let
      fun pred_def' m [] = m
        | pred_def' m bbs = foldl (fn (bb,m) => if BBMap.find (m,bb) = NONE then (pred_def' (BBMap.insert (m,bb,(def bb))) (pred graph bb)) else m) m bbs
    in
      List.concat (BBMap.listItems (pred_def' (map_insert BBMap.empty bb []) (pred graph bb)))
    end
    *)

  fun use bb = let
      fun arg2use code (LLVM.Variable s) = [(s,code)]
        | arg2use _ _ = []
      fun op2use (code as (LLVM.Load (_,_,a))) = arg2use code a
        | op2use (code as (LLVM.GetElementPtr (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Store (_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Add (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Sub (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Mul (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Div (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpEq (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpNe (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpGt (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpGe (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpLt (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.CmpLe (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Br (a))) = arg2use code a
        | op2use (code as (LLVM.CndBr (a,_,_))) = arg2use code a
        | op2use (code as (LLVM.Ret (_,a))) = arg2use code a
        | op2use (code as (LLVM.Print (_,_,a))) = arg2use code a
        | op2use (code as (LLVM.TailPrint (_,_,a))) = arg2use code a
        | op2use (code as (LLVM.And (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Or (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Ashr (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Xor (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Call (_,_,_,args))) = List.concat (map (arg2use code o #1) args)
        | op2use (code as (LLVM.TailCall (_,_,_,args))) = List.concat (map (arg2use code o #1) args)
        | op2use (code as (LLVM.Alias (_,a))) = arg2use code a
        | op2use (code as (LLVM.ZExt (_,_,a1,_))) = (arg2use code a1)
        | op2use (code as (LLVM.SiToFp (_,_,a1,_))) = (arg2use code a1)
        | op2use (code as (LLVM.Bitcast (_,_,a1,_))) = (arg2use code a1)
        | op2use _ = []
      fun equals ((a,_),(b,_)) = a = b
    in
      list_diff' equals (List.concat (map op2use (code bb))) (def bb)
    end

  fun isRealVariable v = (case (explode v) of
      ((#"_")::(#"_")::_) => true
    | _ => false)
  (* find only the use and def that contain __ as the leading characters *)
  fun variables (graph,bbs) = (list_uniqify o (map #1) o List.concat) (map (fn b => (use b)@(def b)) bbs)
  
  (**********************************
   *           IN AND OUT           *
   **********************************)

  fun in_out last_in last_out graph = let
      val (bbgraph,bbs) = graph (*decompose graph*)
      fun equals ((a,_),(b,_)) = a = b
      val new_in = foldl (fn (bb,m) =>
          BBMap.insert (
            m,
            bb,
            (list_union' equals (use bb) (list_diff' equals (map_lookup last_out bb) (def bb)))
            (*(list_diff' equals (list_union (use bb) (map_lookup last_out bb)) (def bb))*)
          )
        ) BBMap.empty bbs
      val new_out = foldl (fn (bb,m) =>
          BBMap.insert (
            m,
            bb,
            (foldl (fn (b,ls) => list_union' equals ls (map_lookup last_in b)) [] (succ graph bb))
          )
        ) BBMap.empty bbs
    in
      if (map_equal' equals last_in new_in) andalso (map_equal' equals last_out new_out) then (new_in,new_out)
      else in_out new_in new_out graph
    end
  val in_out = in_out BBMap.empty BBMap.empty

  
  (**********************************
   *  CREATING BASIC BLOCK GRAPHS   *
   **********************************)

  (* converts a sequence of op codes into a list of basic blocks *)
  fun ops2bblist block [] = [block]
    | ops2bblist block (code::rest) = (case code of
        LLVM.Ret _ => [block@[code]]@(ops2bblist [] rest)
      | LLVM.Br _ => [block@[code]]@(ops2bblist [] rest)
      | LLVM.CndBr _ => [block@[code]]@(ops2bblist [] rest)
      | LLVM.Call _ => [block@[code]]@(ops2bblist [] rest)
      | _ => ops2bblist (block@[code]) rest)
  val ops2bblist = ops2bblist []

  (*annotates a list of basic blocks with their corresponding labels if they have one*)
  fun annotateBBL i [] = []
    | annotateBBL i (((LLVM.DefnLabel label)::coderest)::bbrest) = ((Label (label,i)),(LLVM.DefnLabel label)::coderest)::(annotateBBL (i+1) bbrest)
    | annotateBBL i (bb::bbrest) = (NoLabel i,bb)::(annotateBBL (i+1) bbrest)
  val annotateBBL = annotateBBL 0

  (*takes an annotated list of basic blocks and creates a directed graph from them *)
  exception BadLabel
  fun annotatedBBLToGraph bbs = let
      fun lookup s [] = raise BadLabel
        | lookup s ((Label (s',i),bb)::bbs) = if s = s' then i else lookup s bbs
        | lookup s (_::bbs) = lookup s bbs 

      fun succ id [] = []
        | succ id (code::rest) = (case code of
            LLVM.Ret (_,(LLVM.Label label)) => (lookup label bbs)::(succ id rest)
          | LLVM.Br (LLVM.Label label) => (lookup label bbs)::(succ id rest)
          | LLVM.CndBr (_,LLVM.Label l1,LLVM.Label l2) => (lookup l1 bbs)::((lookup l2 bbs)::(succ id rest))
          | LLVM.Call _ => (id+1)::(succ id rest)
          | _ => succ id rest)

       fun makeEdges graph [] = []
         | makeEdges graph (bb::bbs) = let
            val (_,code) = bb
            val id = (case bb of
                (Label (_,i),_) => i
              | (NoLabel i,_) => i)
            val succs = succ id code
            val _ = map (fn j => Graph.mk_edge {from=Graph.toNode(graph,id), to=Graph.toNode(graph,j)}) succs
          in makeEdges graph bbs end

       val graph = Graph.newGraphOfSize (length bbs)
       val _ = makeEdges graph bbs
    in (graph,bbs) end

  (*chains all the relevant stages together for convienence*)
  fun createBBGraph ops = annotatedBBLToGraph (annotateBBL (List.filter (fn l => length l > 0) (ops2bblist ops)))

  fun createBBList (graph,[]) = []
    | createBBList (graph,bb::bbs) = bb::(createBBList (graph,bbs))
  
end
