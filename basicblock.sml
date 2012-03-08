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


  (* functions for treating lists like sets *)
  (* for each element in xs, filter the remaining list *)
  (* non order preserving *)
  fun list_uniqify xs = foldl (fn (x,xs) => x::(List.filter (fn y => x<>y) xs) ) xs xs
  (*subtracts the contents of list b from list a*)
  fun list_diff equals a [] = a
    | list_diff equals a (b::bs) = list_diff equals (List.filter (fn x => not (equals (b,x))) a) bs
  fun list_diff' e a b = list_uniqify (list_diff e a b)
  val list_diff = (list_diff (op =)) o list_uniqify 
  fun list_union a b = list_uniqify (a@b)
  (*returns true if two lists are set-wise equal*)
  fun list_equal [] [] = true
    | list_equal [] _ = false
    | list_equal _ [] = false
    | list_equal (x::xs) ys = let
      fun rm ls = List.filter (fn z => z<>x) ls
      in list_equal (rm xs) (rm ys) end

  (*functions for dealing with maps of basic blocks to lists*)
  structure BBMap = RedBlackMapFn (struct
      type ord_key = BasicBlock
      val compare = (fn ((xl,_),(yl,_)) => Int.compare( label2int xl, label2int yl))
    end)
  fun map_lookup m key = (case BBMap.find (m,key) of
        NONE => []
      | SOME v => v)
  fun map_equal m1 m2 = let
    fun oneway m1 m2 = BBMap.foldli (fn (k,v,b) => if list_equal (map_lookup m2 k) v then b else false) true m1
    in oneway m1 m2 andalso oneway m2 m1 end

(* functions for getting relevant info out of a basic block *)
  exception NoSuchBlock

  fun id2bb (graph,[]) id = raise NoSuchBlock
    | id2bb (graph,((label,bb)::bs)) id = if label2int label = id then (label,bb) else id2bb (graph,bs) id

  fun code (_,code) = code
  fun label (label,_) = concat ["BB",Int.toString(label2int label)]
  fun succ (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.succ (Graph.toNode (graph,label2int label)))
  fun pred (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.pred (Graph.toNode (graph,label2int label)))

  fun def bb = let
      fun op2def (code as (LLVM.Load (s,_,_))) = [(s,code)]
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
        | op2def (code as (LLVM.Alloca (s,_))) =  [(s,code)]
        | op2def (code as (LLVM.Ashr (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Xor (s,_,_,_))) =  [(s,code)]
        | op2def (code as (LLVM.Call (s,_,_,_))) =  [(s,code)]
        | op2def _ = []
    in
      List.concat (map op2def (code bb))
    end

  fun use bb = let
      fun arg2use code (LLVM.Variable s) = [(s,code)]
        | arg2use _ _ = []
      fun op2use (code as (LLVM.Load (_,_,a))) = arg2use code a
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
        | op2use (code as (LLVM.And (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Or (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Ashr (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Xor (_,_,a1,a2))) = (arg2use code a1)@(arg2use code a2)
        | op2use (code as (LLVM.Call (_,_,_,args))) = List.concat (map (arg2use code) args)
        | op2use _ = []
    in
      List.concat (map op2use (code bb))
    end

  (* Previous definitions
    fun vars_in graph bb = list_union (use bb) (list_diff (vars_out graph bb) (def bb))
    and vars_out graph bb = List.concat (map (vars_in graph) (succ graph bb))
  *)
  (* String*OP set
  structure SOPSet = RedBlackSetFn (struct
      type ord_key = string
      val compare = String.compare
    end)
  *)

  fun in_out last_in last_out graph = let
      val (bbgraph,bbs) = graph (*decompose graph*)
      fun equals ((a,_),(b,_)) = a = b
      val new_in = foldl (fn (bb,m) =>
          BBMap.insert (
            m,
            bb,
            (list_union (use bb) (list_diff' equals (map_lookup last_out bb) (def bb)))
          )
        ) BBMap.empty bbs
      val new_out = foldl (fn (bb,m) =>
          BBMap.insert (
            m,
            bb,
            (foldl (fn (b,ls) => list_union ls (map_lookup last_in b)) [] (succ graph bb))
          )
        ) BBMap.empty bbs
    in
      if (map_equal last_in new_in) andalso (map_equal last_out new_out) then (new_in,new_out)
      else in_out new_in new_out graph
    end
  val in_out = in_out BBMap.empty BBMap.empty

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

  fun toDot title bbgraph = let
      val (graph,bbs) = bbgraph
      val (bbin,bbout) = in_out bbgraph
      fun fixendl [] = []
        | fixendl (c::cs) = if (str c) = "\n" then (explode "\\n")@(fixendl cs) else c::(fixendl cs)
      fun combine glue lst = foldr (fn (a,b) => concat [a,glue,b]) "" lst
      fun stripcode [] = []
        | stripcode ((s,code)::xs) = s::(stripcode xs)
      fun definitions [] = []
        | definitions ((bb as (label,code))::rest) = (concat [
            "\tBB", Int.toString(label2int label)," [label=\"",
              (implode (fixendl (explode (combine "\\n" (map LLVM.printOP code))))),
              "\\n\\nuse: ",(combine ", " (stripcode (use bb))),
              "\\ndef: ",(combine ", " (stripcode (def bb))),
              "\\n\\nin: ",(combine ", " (stripcode (map_lookup bbin bb))),
              "\\nout: ",(combine ", " (stripcode (map_lookup bbout bb))),
              "\"];\n",
            "\tBB", Int.toString(label2int label)," [shape=box];" ])::(definitions rest)
      fun edges [] = []
        | edges ((label,code)::rest) = (combine "\n" (map (fn i => (concat [
            "\tBB", Int.toString(label2int label)," -> BB",Int.toString(Graph.toInt i),";" ])) (Graph.succ (Graph.toNode(graph,label2int label)))))::(edges rest)
    in
      concat [
          "digraph ",title," {\n"
        , (combine "\n" (definitions bbs))
        , (combine "\n" (edges bbs))
        , "\n}\n" ]
    end

end
