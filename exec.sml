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
    fun print_error (s,i:int,_) =
      TextIO.output(TextIO.stdOut,"Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
  in
    EvalParser.parse(0,lexstream,print_error,())
  end

val lexer = EvalParser.makeLexer (inputc TextIO.stdIn)

val (result,lexer) = invoke lexer
val _ = if debug then showTree 0 result else ()
val _ = showValue (eval (result,[]))

