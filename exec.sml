(*Will Coster*)

(*This file contains the code for the executable*)

fun inputc instrm i = TextIO.inputN(instrm,i);
val lexer = EvalLex.makeLexer (inputc TextIO.stdIn);
(*
val ast = ((parse lexer) handle ParserError s => let
    val _ = print (concat ["Parser Error: ",s])
  in
    (Num 0)
  end)
*)

fun indent 0 str= print (concat [str,"\n"])
  | indent x str = let val _ = print "  " in indent (x-1) str end

fun showTree x (Var str) = indent x (concat ["Var(",str,")"])
  | showTree x (Num i) = indent x (concat ["Num(",Int.toString(i),")"])
  | showTree x (Plus (e1,e2)) = let
      val _ = indent x "Plus"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Minus (e1,e2)) = let
      val _ = indent x "Minus"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Div (e1,e2)) =  let
      val _ = indent x "Div"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Mult (e1,e2)) =  let
      val _ = indent x "Mult"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Apply (e1,e2)) =  let
      val _ = indent x "Apply"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Let (str,e1,e2)) =  let
      val _ = indent x (concat ["Let(",str,")"])
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (LetSta (f,y,e1,e2)) = let
      val _ = indent x (concat ["LetSta( ",f,"(",y,") )"])
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (LetDyn (f,y,e1,e2)) = let
      val _ = indent x (concat ["LetDyn( ",f,"(",y,") )"])
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end

fun parseAndRun lex = let
    val v = (0,(parse (lex)),"") handle (ParserError s) => (1,(Num 0),s);
  in
    (case v of
      (0,ast,_) => let
          val _ = if debug then print "Parse Tree:\n" else ()
          val _ = if debug then showTree 0 ast else ()
        in
          (evalAndShow (ast,[]))
        end
      | (1,_,error) => (print (concat ["ParserError: ",error,"\n"]))
      | _ => (print "How did you even get here?\n"))
  end;

parseAndRun lexer;
