(* Will Coster *)

structure BB = 
struct
  
(*Basic blocks are lists of op codes *)
  type BasicBlock = LLVM.OP list

(* converts an LLVM.OP list to a list of basic blocks *)
  fun ops2blocks curblock (code::rest) = case code of
      LLVM.Ret _ => [curblock@[code]]
    | LLVM.Br _ => (ops2blocks [] rest)@[curblock@[code]]
    | LLVM.CndBr _ => (ops2blocks [] rest)@[curblock@[code]]
    | LLVM.Call _ => (ops2blocks [] rest)@[curblock@[code]]
    | _ => ops2blocks (curblock@[code]) rest

(* provide a default value for curblock in ops2blocks *)
  val ops2blocks = ops2blocks []

  (*fun showBasicBlocks (bb::bs) = *)

end
