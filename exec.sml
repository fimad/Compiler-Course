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

(*for parsing arguments *)
fun shouldArg arg = List.foldr (fn (x,b) => (x = arg) orelse b) false (CommandLine.arguments ())
(*parses an argument and returns a maybe numeric argument*)
fun shouldArgNum arg = List.foldr (fn (x,b) => 
    let
      val x_list = explode x
      val num_str = implode (List.drop (x_list,length (explode arg)))
      val num = Int.fromString num_str
    in
      if (not (isSome b) andalso String.isPrefix arg x) then num else b
    end
    ) NONE (CommandLine.arguments ())

(*should we do optimizations?*)
val optimizeLevel = case shouldArgNum "-O" of (SOME i) => i | _ => 0

(*should we do loop unrolling?*)
val loopUnroll = shouldArgNum "-LU"
val _ = LLVM_Translate.setUnrollAmount loopUnroll
(*should we also try to vectorize loops*)
val _ = LLVM_Translate.setVectorize (shouldArg "-V")

(*should we echo dot output?*)
val shouldDot = shouldArg "-dot"
(*should we annotate dot output?*)
val shouldAnnotate = shouldArg "-v"

(*Compile and catch any errors!*)
val _ = LLVM_Translate.compile result handle (LLVM_Translate.TranslationError what) => let
    val _ = (print (concat ["Translation Error: ",what,"\n"]), OS.Process.exit OS.Process.failure)
    in () end
  handle (LLVM.LLVMError what) => let
    val _ = (print (concat ["Translation Error: ",what,"\n"]), OS.Process.exit OS.Process.failure)
    in () end

val program = LLVM_Translate.getProgram ()

fun optimizeMethod (name,ty,args,code) = let
    val bbGraph = SSA.completeSSA (BB.createBBGraph code)
  in
    (name,ty,args,((BB.graph2code o (Optimize.optimize optimizeLevel)) bbGraph))
  end
fun method2dot (title,_,_,code) = DOT.toDot title (Optimize.optimize optimizeLevel (SSA.completeSSA (BB.createBBGraph code))) shouldAnnotate

val _ = if shouldDot
  then print (concat (map method2dot program))
  else print (LLVM.printProgram (map optimizeMethod program))
