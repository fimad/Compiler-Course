(*Will Coster*)

signature AST =
sig
  (* Definition of the AST
   * ast is a datatype encapsulating the abstract syntax of the language e *)
  datatype ast
    = Var of string
    | Num of int
    (*digit arith*)
    | Plus of ast*ast
    | Minus of ast*ast
    | Div of ast*ast
    | Mult of ast*ast
    (*boolean arith*)
    | Not of ast
    | Eq of ast*ast
    | Less of ast*ast
    | Apply of ast*(ast list)
    | If of ast*ast*ast
    | Let of string*ast*ast
    | LetSta of string*(string list)*ast*ast
    | LetDyn of string*(string list)*ast*ast
  (*
   * enval is a datatype that covers the possible values that can be stored in the
   * environment. As of now this includes, the various functions and integers
   *)
  datatype enval
    = Val of int
    (* Functions contain a parameter identifier, an expression, and some
     * expression for setting local environment
     * static bound also includes a snapshot of the global environment when it
     * was created
     *)
    | FSta of (string list)*ast*((string*enval) list)
    | FDyn of (string list)*ast

(*
 * a datatype for the return value of the eval function.
 * Eval can either return an error message, or a success of a value and a new
 * environment.
 *)
  datatype evalret
    = Error of string
    | Success of enval
end

structure Ast :> AST = 
struct
  datatype ast
    = Var of string
    | Num of int
    | Plus of ast*ast
    | Minus of ast*ast
    | Div of ast*ast
    | Mult of ast*ast
    | Not of ast
    | Eq of ast*ast
    | Less of ast*ast
    | Apply of ast*(ast list)
    | If of ast*ast*ast
    | Let of string*ast*ast
    | LetSta of string*(string list)*ast*ast
    | LetDyn of string*(string list)*ast*ast

  datatype enval
    = Val of int
    | FSta of (string list)*ast*((string*enval) list)
    | FDyn of (string list)*ast

  datatype evalret
    = Error of string
    | Success of enval
end

fun indent 0 str= print (concat [str,"\n"])
  | indent x str = let val _ = print "  " in indent (x-1) str end
and showStringList i [] = ()
  | showStringList i (e::es) = let
    val _ = indent i e
  in
    showStringList i es
  end
and showList i [] = ()
  | showList i (e::es) = let
    val _ = showTree i e
  in
    showList i es
  end
and showTree x (Ast.Var str) = indent x (concat ["Var(",str,")"])
  | showTree x (Ast.Num i) = indent x (concat ["Num(",Int.toString(i),")"])
  | showTree x (Ast.Eq (e1,e2)) = let
      val _ = indent x "Eq"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Less (e1,e2)) = let
      val _ = indent x "Less"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Not (e1)) = let
      val _ = indent x "Not"
      val _ = showTree (x+1) e1
    in () end
  | showTree x (Ast.Plus (e1,e2)) = let
      val _ = indent x "Plus"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Minus (e1,e2)) = let
      val _ = indent x "Minus"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Div (e1,e2)) =  let
      val _ = indent x "Div"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Mult (e1,e2)) =  let
      val _ = indent x "Mult"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.Apply (e1,e2)) =  let
      val _ = indent x "Apply"
      val _ = showTree (x+1) e1
      val _ = showList (x+1) e2
    in () end
  | showTree x (Ast.If (e1,e2,e3)) =  let
      val _ = indent x "If("
      val _ = showTree (x+1) e1
      val _ = indent x ")"
      val _ = showTree (x+1) e2
      val _ = showTree (x+1) e3
    in () end
  | showTree x (Ast.Let (str,e1,e2)) =  let
      val _ = indent x (concat ["Let(",str,")"])
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.LetSta (f,y,e1,e2)) = let
      val _ = indent x (concat ["LetSta( ",f,"("])
      val _ = showStringList (x+1) y
      val _ = indent x ") )"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
  | showTree x (Ast.LetDyn (f,y,e1,e2)) = let
      val _ = indent x (concat ["LetDyn( ",f,"("])
      val _ = showStringList (x+1) y
      val _ = indent x ") )"
      val _ = showTree (x+1) e1
      val _ = showTree (x+1) e2
    in () end
      
(*Pretty print functions for enval*)
fun showValue (Ast.Success (Ast.Val i)) = print ((Int.toString(i))^"\n")
  | showValue (Ast.Success (Ast.FSta _)) = print ("Static function...\n")
  | showValue (Ast.Success (Ast.FDyn _)) = print ("Dynamic function...\n")
  | showValue (Ast.Error s) = print (s^"\n")

val debug = true
