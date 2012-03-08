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
  fun list_diff a [] = a
    | list_diff a (b::bs) = list_diff (List.filter (fn x => b <> x) a) bs
  val list_diff = list_diff o list_uniqify 
  fun list_union a b = list_uniqify a@b
  (*returns true if two lists are set-wise equal*)
  fun list_equal [] [] = true
    | list_equal [] _ = false
    | list_equal _ [] = false
    | list_equal (x::xs) ys = let
      fun rm ls = List.filter (fn z => z<>x) ls
      in list_equal (rm xs) (rm ys) end

(* functions for getting relevant info out of a basic block *)
  exception NoSuchBlock

  fun id2bb (graph,[]) id = raise NoSuchBlock
    | id2bb (graph,((label,bb)::bs)) id = if label2int label = id then (label,bb) else id2bb (graph,bs) id

  fun code (_,code) = code
  fun label (label,_) = concat ["BB",Int.toString(label2int label)]
  fun succ (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.succ (Graph.toNode (graph,label2int label)))
  fun pred (graph,bbs) (label,_) = map (fn x => (id2bb (graph,bbs) (Graph.toInt x))) (Graph.pred (Graph.toNode (graph,label2int label)))

  fun def bb = let
      fun op2def (LLVM.Load (s,_,_)) = [s]
        | op2def (LLVM.Add (s,_,_,_)) = [s]
        | op2def (LLVM.Sub (s,_,_,_)) = [s]
        | op2def (LLVM.Mul (s,_,_,_)) = [s]
        | op2def (LLVM.Div (s,_,_,_)) = [s]
        | op2def (LLVM.CmpEq (s,_,_,_)) = [s]
        | op2def (LLVM.CmpNe (s,_,_,_)) = [s]
        | op2def (LLVM.CmpGt (s,_,_,_)) = [s]
        | op2def (LLVM.CmpGe (s,_,_,_)) = [s]
        | op2def (LLVM.CmpLt (s,_,_,_)) = [s]
        | op2def (LLVM.CmpLe (s,_,_,_)) = [s]
        | op2def (LLVM.And (s,_,_,_)) = [s]
        | op2def (LLVM.Or (s,_,_,_)) = [s]
        | op2def (LLVM.Alloca (s,_)) = [s]
        | op2def (LLVM.Ashr (s,_,_,_)) = [s]
        | op2def (LLVM.Xor (s,_,_,_)) = [s]
        | op2def (LLVM.Call (s,_,_,_)) = [s]
        | op2def _ = []
    in
      List.concat (map op2def (code bb))
    end

  fun use bb = let
      fun arg2use (LLVM.Variable s) = [s]
        | arg2use _ = []
      fun op2use (LLVM.Load (_,_,a)) = arg2use a
        | op2use (LLVM.Store (_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Add (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Sub (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Mul (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Div (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpEq (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpNe (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpGt (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpGe (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpLt (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.CmpLe (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Br (a)) = arg2use a
        | op2use (LLVM.CndBr (a,_,_)) = arg2use a
        | op2use (LLVM.Ret (_,a)) = arg2use a
        | op2use (LLVM.And (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Or (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Ashr (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Xor (_,_,a1,a2)) = (arg2use a1)@(arg2use a2)
        | op2use (LLVM.Call (_,_,_,args)) = List.concat (map arg2use args)
        | op2use _ = []
    in
      List.concat (map op2use (code bb))
    end

  (* Previous definitions
    fun vars_in graph bb = list_union (use bb) (list_diff (vars_out graph bb) (def bb))
    and vars_out graph bb = List.concat (map (vars_in graph) (succ graph bb))
  *)
  structure SetT = RedBlackSetFn (struct
      type ord_key = string
      val compare = String.compare
    end)

  structure BBMap = RedBlackMapFn (struct
      type ord_key = BasicBlock
      val compare = (fn ((xl,_),(yl,_)) => Int.compare( label2int xl, label2int yl))
    end)

  (*
  fun list2bbmap xs = foldl (fn (x,map) => BBMap.insert(map,x)) BBMap.empty xs
  *)

  fun bbdiff a b = BBMap.filter (fn x => case BBMap.find (b,x) of
        SOME _ => false
      | NONE => true ) a

  (*
  fun in_out last_in last_out graph = let
      val (bbgraph,bbs) = graph (*decompose graph*)
      val new_in = foldl (fn (bb,map) => BBMap.unionWith (fn (x,_) => x) (list2bbmap (use bb)) (bbdiff last_out (list2bbmap (def bb)))) BBMap.empty bbs
      val new_out = 
    in
    end
  val in_out = in_out BBMap.empty BBMap.empty
  *)

  (*
  fun in_out last_in last_out graph bb = let
      val new_in = list_union (use bb) (list_diff last_out (def bb))
      val new_out = list_uniqify List.concat (map (
    in

    end
  val in_out = in_out [] []
  *)

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
      fun fixendl [] = []
        | fixendl (c::cs) = if (str c) = "\n" then (explode "\\n")@(fixendl cs) else c::(fixendl cs)
      fun combine glue lst = foldr (fn (a,b) => concat [a,glue,b]) "" lst
      fun definitions [] = []
        | definitions ((label,code)::rest) = (concat [
            "\tBB", Int.toString(label2int label)," [label=\"",
              (implode (fixendl (explode (combine "\\n" (map LLVM.printOP code))))),
              "\\n\\nuse: ",(combine ", " (use (label,code))),
              "\\ndef: ",(combine ", " (def (label,code))),
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
