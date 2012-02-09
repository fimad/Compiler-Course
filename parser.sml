(*Will Coster*)

(* The grammar for this parser is 
statement = expression | let | letsta | letdyn
expression = term | term+expression | term-expression
term = factor | factor*term | factor/term
factor = tLParen expression tRParen | tNum | tID | tID tLParen expression tRParen
let = tLet tID tEq statement tIn statement
letsta = tLetSta tID tLParen tID tRParen tEq statement tIn statement
letdyn = tLetDyn tID tLParen tID tRParen tEq statement tIn statement
 *)

exception ParserError of string
 
fun parse lexer = let
  open EvalLex
  open UserDeclarations
(*pull out all of the tokens into a list*)
    fun grabAllTokens EOF = [EOF]
      | grabAllTokens t = t::(grabAllTokens (lexer()))
    val tokens = grabAllTokens (lexer())
(*debug methods*)
    fun tokensToStringList [] = []
      | tokensToStringList ((tID str)::ts) = "ID("::str::") "::tokensToStringList(ts)
      | tokensToStringList ((tNum i)::ts) = "Num("::Int.toString(i)::") "::tokensToStringList(ts)
      | tokensToStringList (tEqual::ts) = "Equal "::tokensToStringList(ts)
      | tokensToStringList (tPlus::ts) = "Plus "::tokensToStringList(ts)
      | tokensToStringList (tMinus::ts) = "Minus "::tokensToStringList(ts)
      | tokensToStringList (tDiv::ts) = "Div "::tokensToStringList(ts)
      | tokensToStringList (tMult::ts) = "Mult "::tokensToStringList(ts)
      | tokensToStringList (tLet::ts) = "Let "::tokensToStringList(ts)
      | tokensToStringList (tIn::ts) = "In "::tokensToStringList(ts)
      | tokensToStringList (tLetSta::ts) = "LetSta "::tokensToStringList(ts)
      | tokensToStringList (tLetDyn::ts) = "LetDyn "::tokensToStringList(ts)
      | tokensToStringList (tLParen::ts) = "LParen "::tokensToStringList(ts)
      | tokensToStringList (tRParen::ts) = "RParen "::tokensToStringList(ts)
      | tokensToStringList (tEOF::ts) = "EOF "::tokensToStringList(ts)
    fun showTokens tokens = print (concat ((tokensToStringList tokens)@["\n"]))
    val _ = if debug then print "Lex: " else ()
    val _ = if debug then showTokens tokens else ()
(*functions for a recursive descent parser*)
    fun statement (tLet::ts) = p_let (tLet::ts)
      | statement (tLetSta::ts) = letsta (tLetSta::ts)
      | statement (tLetDyn::ts) = letdyn (tLetDyn::ts)
      | statement tokens = expression tokens
    and p_let (tLet::(tID (id))::tEq::ts) = let
          val (s1,(s2,ts)) = case (statement ts) of 
              (s1,(tIn::ts)) => (s1,statement ts)
              | (_,tokens) => raise ParserError (concat ("expected In, got: "::(tokensToStringList tokens)))
        in
          (Let (id,s1,s2),ts)
        end
      | p_let tokens = raise ParserError (concat ("expected Let ID Equals, got: "::(tokensToStringList tokens)))
    and letsta (tLetSta::(tID (f))::tLParen::(tID (x))::tRParen::tEq::ts) = let
          val (s1,(s2,ts)) = case (statement ts) of 
              (s1,(tIn::ts)) => (s1,statement ts)
              | (_,tokens) => raise ParserError (concat ("expected In, got: "::(tokensToStringList tokens)))
        in
          (LetSta (f,x,s1,s2),ts)
        end
      | letsta tokens = raise ParserError (concat ("expected letsta f(x) =, got: "::(tokensToStringList tokens)))
    and letdyn (tLetDyn::(tID (f))::tLParen::(tID (x))::tRParen::tEq::ts) = let
          val (s1,(s2,ts)) = case (statement ts) of 
              (s1,(tIn::ts)) => (s1,statement ts)
              | (_,tokens) => raise ParserError (concat ("expected In, got: "::(tokensToStringList tokens)))
        in
          (LetDyn (f,x,s1,s2),ts)
        end
      | letdyn tokens = raise ParserError (concat ("expected letdyn f(x) =, got: "::(tokensToStringList tokens)))
    and expression tokens = let
          val (f1,oper,ts) = case (term tokens) of
              (f1,(tPlus::ts)) => (f1,tPlus,ts)
              | (f1,(tMinus::ts)) => (f1,tMinus,ts)
              | (f1,ts) => (f1,EOF,ts)
          val (f2,ts) = if oper = EOF then (Num(0),ts) else expression ts
        in
          if oper = EOF then (f1,ts) else
            if oper = tPlus then (Plus (f1,f2),ts) else (Minus (f1,f2),ts)
        end
    and term tokens = let
          val (f1,oper,ts) = case (factor tokens) of
              (f1,(tMult::ts)) => (f1,tMult,ts)
              | (f1,(tDiv::ts)) => (f1,tDiv,ts)
              | (f1,ts) => (f1,EOF,ts)
          val (f2,ts) = if oper = EOF then (Num(0),ts) else term ts
        in
          if oper = EOF then (f1,ts) else
            if oper = tMult then (Mult (f1,f2),ts) else (Div (f1,f2),ts)
        end
    and factor (tLParen::ts) = (case (expression ts) of
        (exp,(tRParen::ts)) => (exp,ts)
        | (_,tokens) => raise ParserError (concat ("expected RParen, got: "::(tokensToStringList tokens))))
      | factor ((tID(x))::tLParen::ts) = let
          val (exp,ts) = case (expression ts) of 
              (exp,tRParen::ts) => (exp,ts)
              | (_,tokens) => raise ParserError (concat ("expected RParen, got: "::(tokensToStringList tokens)))
        in
          (Apply (Var(x),exp), ts)
        end
      | factor ((tID(x))::ts) = (Var(x),ts)
      | factor ((tNum(i))::ts) = (Num(i),ts)
      | factor tokens = raise ParserError (concat ("expected ID or Num, got: "::(tokensToStringList tokens)))
  in
    case (statement tokens) of 
      (ast,[EOF]) => ast
      | _ => raise ParserError "unexpected tokens at end of stream"
  end;

