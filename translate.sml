(* Will Coster *)

open Ast

(*
 * a datatype for the return value of the translate function.
 * Eval can either return an error message, or a success
 * environment.
 *)
datatype transret
  = Error of string
  | Success


(*Helper methods for echoing opts and returning success*)
fun sayopt0 opt = let
  val _ = print (concat [opt,"\n"])
  in Success end
fun sayopt1 opt arg = let
  val _ = print (concat [opt," ",arg,"\n"])
  in Success end
fun saylabel label = let
  val _ = print (concat [label,":\n"])
  in Success end

(*next label prints out the next generic label, useful for if statements*)
val curlabel = ref 0

(*what would be the next label?*)
fun nextlabel () = concat ["L",Int.toString(!curlabel)]

(*what's the next label? and advance the counter?*)
fun makenextlabel () = let
    val label = nextlabel ()
    val _ = (curlabel := !curlabel+1)
  in label end

(*return the first error in list or return success*)
fun test_error [] = Success
  | test_error (Success::xs) = test_error xs
  | test_error (error::xs) = error

fun translate (Num (i)) = sayopt1 "pushnum" (Int.toString(i))
  | translate (Var (x)) = sayopt1 "pushvar" x
  | translate (Eq (a,b)) = 
    test_error [
        translate a
      , translate b
      , sayopt0 "cmpeq"
    ]
  | translate (Less (a,b)) = 
    test_error [
        translate a
      , translate b
      , sayopt0 "cmplt"
    ]
  | translate (Not (a)) =
    test_error [
        translate a
      , sayopt0 "not"
    ]
  | translate (Plus (a,b)) =
    test_error [
        translate a
      , translate b
      , sayopt0 "add"
    ]
  | translate (Minus (a,b)) = 
    test_error [
        translate a
      , translate b
      , sayopt0 "sub"
    ]
  | translate (Mult (a,b)) =
    test_error [
        translate a
      , translate b
      , sayopt0 "mul"
    ]
  | translate (Div (a,b)) =
    test_error [
        translate a
      , translate b
      , sayopt0 "div"
    ]
  | translate (Apply ((Var v),exps)) = 
    test_error ((map translate exps)@[sayopt1 "call" v])
  | translate (Apply _) =  Error "Can only apply on variables"
  | translate (If (bexp,texp,fexp)) = let
      val l1 = makenextlabel ()
      val l2 = makenextlabel ()
    in
      test_error [
          translate bexp
        , sayopt1 "jz" l1
        , translate texp
        , sayopt1 "jmp" l2
        , saylabel l1
        , translate fexp
        , saylabel l2
      ]
    end
  | translate (Let (id,exp,inexp)) = 
    test_error [
        translate exp
      , sayopt1 "popvar" id
      , translate inexp
    ]
  | translate (LetSta (fid,xids,fexp,inexp)) = let
      val l = makenextlabel ()
    in
      test_error ([
          sayopt1 "jmp" l
        , saylabel fid ] @
        (map (sayopt1 "popvar") xids) @ [
          translate fexp
        , saylabel l
        , translate inexp
      ])
    end
  | translate (LetDyn (fid,xids,fexp,inexp)) = let
      val l = makenextlabel ()
    in
      test_error ([
          sayopt1 "jmp" l
        , saylabel fid ] @
        (map (sayopt1 "popvar") xids) @ [
          translate fexp
        , saylabel l
        , translate inexp
      ])
    end

fun showTransValue Success = print "\nSuccess!\n"
  | showTransValue (Error s) = print (concat ["Error: ",s,"\n"])
