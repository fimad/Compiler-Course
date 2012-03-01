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

val _ = LLVM_Translate.compile result 
val program = LLVM_Translate.getProgram ()
fun method2dot (title,_,_,code) = BB.toDot title (BB.createBBGraph code)
val _ = print (concat (map method2dot program))

(*val _= print (BB.makeDot (BB.labelBlocks (LLVM_Translate.getProgram ())))*)
(*val _ = print (LLVM.printProgram (LLVM_Translate.getProgram ()))*)

