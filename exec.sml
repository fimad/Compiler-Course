(*Will Coster*)

(*This file contains the code for the executable*)

fun inputc instrm i = TextIO.inputN(instrm,i);
(*val lexer = EvalLex.makeLexer (inputc TextIO.stdIn);*)
(*
val ast = ((parse lexer) handle ParserError s => let
    val _ = print (concat ["Parser Error: ",s])
  in
    (Num 0)
  end)
parseAndRun lexer;
*)

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

(*
fun parse () = let 
    fun loop lexer = let
        val (result,lexer) = invoke lexer
        val (nextToken,lexer) = EvalParser.Stream.get lexer
      in
        showValue (eval (result,[]))
      end
    val lexer = EvalParser.makeLexer (inputc TextIO.stdIn)
  in
    loop lexer
  end

parse ();
*)
