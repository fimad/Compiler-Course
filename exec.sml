(*Will Coster*)

(*This file contains the code for the executable*)

fun inputc instrm i = TextIO.inputN(instrm,i);

structure EvalLrVals =
  EvalLrValsFun(
      structure Token = LrParser.Token
      structure Ast = Ast
  )

structure EvalLex =
  EvalLexFun(structure Tokens = EvalLrVals.Tokens);

structure EvalParser =
  Join(structure LrParser = LrParser
    structure ParserData = EvalLrVals.ParserData
    structure Lex = EvalLex)

fun invoke lexstream = let
    fun print_error (s,i:int,_) = let
        val _ = TextIO.output(TextIO.stdOut,"Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
        val _ =  OS.Process.exit OS.Process.failure (*force quit, o/w mlyacc inf loops*)
      in () end
  in
    EvalParser.parse(0, lexstream, print_error, ())
  end

(*parse the input*)
val lexer = EvalParser.makeLexer (inputc TextIO.stdIn)
val (result,lexer) = invoke lexer

(*
(*find out if we should compile or interpret*)
val shouldEval = List.foldr (fn (x,b) => (x = "-eval") orelse b) false (CommandLine.arguments ())

val _ = if debug then showTree 0 result else ()
val _ = if shouldEval then
          showValue (eval (result,[]))
        else 
          (*showTransValue (translate result)*)
          let
            val _ = LLVM_Translate.compile result
          in
            print (LLVM.printProgram (LLVM_Translate.getProgram ()))
          end
          *)
fun shouldArg arg = List.foldr (fn (x,b) => (x = arg) orelse b) false (CommandLine.arguments ())
val shouldO1 = shouldArg "-O1"
val shouldO2 = shouldArg "-O2"
val optimizeLevel =
  if shouldArg "-O2" then 2 else
  if shouldArg "-O1" then 1 else
  0;
val shouldDot = shouldArg "-dot"

val _ = LLVM_Translate.compile result 
val program = LLVM_Translate.getProgram ()
val bbGraph = SSA.resolvePhi (BB.createBBGraph code)
fun optimizeMethod (name,ty,args,code) = (name,ty,args,((BB.graph2code o (Optimize.optimize optimizeLevel)) bbGraph))
fun method2dot (title,_,_,code) = BB.toDot title (Optimize.optimize optimizeLevel (BB.createBBGraph code))
val _ = if shouldDot
  then print (concat (map method2dot program))
  else print (LLVM.printProgram (map optimizeMethod program))

(*val _= print (BB.makeDot (BB.labelBlocks (LLVM_Translate.getProgram ())))*)
(*val _ = print (LLVM.printProgram (LLVM_Translate.getProgram ()))*)

