(*Will Coster*)

(* Definition of the AST
 * exp is a datatype encapsulating the abstract syntax of the language e *)
datatype exp
  = Var of string
  | Num of int
  | Plus of exp*exp
  | Minus of exp*exp
  | Div of exp*exp
  | Mult of exp*exp
  | Apply of exp*exp
  | Let of string*exp*exp
  | LetSta of string*string*exp*exp
  | LetDyn of string*string*exp*exp

val debug = false
