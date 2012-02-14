(* Will Coster *)

open Ast

(*
 * lookup searches an environment (Which is a list of string enval*pairs) for a
 * given identifier.
 * It returns SOME enval if found and NONE if it is not in the environment
 *)
fun lookup (id,[]) = NONE
  | lookup (id,(pid,pval)::ps) = if id=pid then SOME pval else lookup (id, ps)

fun eval (Num (i), p) = Success (Val i)
  | eval (Var (x), p) = (case lookup(x, p) of
    SOME v => Success v
    | NONE => Error (concat ["Variable `",x,"` is not in the environment"]))
  | eval (Eq (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (if anum = bnum then 1 else 0))
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Less (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (if anum < bnum then 1 else 0))
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Not (a), p) = (case (eval (a,p)) of
      (Success (Val anum)) =>
          Success (Val (if anum = 0 then 1 else 0))
      | (Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Plus (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (*if we have proper values, pull out the ints and add them together*)
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (anum+bnum))
      (*
       * If one of the values evaluates to an error, or if there is a type
       * mismatch, report an error
       *)
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Minus (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (*if we have proper values, pull out the ints and sub them*)
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (anum-bnum))
      (*
       * If one of the values evaluates to an error, or if there is a type
       * mismatch, report an error
       *)
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Mult (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (*if we have proper values, pull out the ints and times them together*)
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (anum*bnum))
      (*
       * If one of the values evaluates to an error, or if there is a type
       * mismatch, report an error
       *)
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Div (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (*if we have proper values, pull out the ints and div them together*)
      (Success (Val anum), Success (Val bnum)) =>
          Success (Val (anum div bnum))
      (*
       * If one of the values evaluates to an error, or if there is a type
       * mismatch, report an error
       *)
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Apply (fexp,exps), p) =  let
      (*zips a list with a constant*)
      fun rzip [] _ = []
        | rzip (x::xs) c = (x,c)::(rzip xs c)
      (*zips ids with evaluated exps*)
      fun help fids exps = ListPair.zip (fids,(map (fn x => let val (Success v) = eval x in v end) (rzip exps p)))
    in
      (*evaluate both sides sides of the apply*)
      (case (eval (fexp,p)) of
        (*
         * if the function value is is a statif or dynamic function, pull out
         * the relevant bits and pass to apply helper
         *)
        (Success (FSta (fids,fexp,fp))) =>
            eval (fexp,(help fids exps)@fp)
        | (Success (FDyn (fids,fexp))) =>
            eval (fexp,(help fids exps)@p)
        (*Otherwise report the error that occured*)
        | (Error s) => Error s
        | _ => Error "Attempt to apply with a non-function value")
      end
  | eval (If (bexp,texp,fexp), p) = (case eval (bexp,p) of 
    Success (Val 0) => eval (fexp,p)
    | Success _ => eval (texp,p)
    | Error s => Error s)
  | eval (Let (id,exp,inexp), p) = (case eval (exp,p) of 
    Success v => eval (inexp,(id,v)::p)
    | Error s => Error s)
  (*
   * The let for functions are fairly straight forward, they just copy the
   * supplied expression and strings into the correct structures.
   *)
  | eval (LetSta (fid,xid,fexp,inexp), p) = let
      val f = FSta (xid,fexp,p)
    in
      eval (inexp,(fid,f)::p)
    end
  | eval (LetDyn (fid,xid,fexp,inexp), p) = let
      val f = FDyn (xid,fexp)
    in
      eval (inexp,(fid,f)::p)
    end

(*evaluate and print an expression
fun evalAndShow x = showValue (eval x)
*)

(*
 Prelexer tests
(*
let a = 0 in
letsta add(x) = x + a in
let a = 5 in
add(5)
 *)
val static_test = Let ("a",Num 0,(LetSta ("add","x",Plus (Var "x", Var "a"),Let ("a",Num 5, Apply (Var "add", Num 5)))));
val dynamic_test = Let ("a",Num 0,(LetDyn ("add","x",Plus (Var "x", Var "a"),Let ("a",Num 5, Apply (Var "add", Num 5)))));

(*result should be 5*)
evalAndShow (static_test,[]);
(*result should be 10*)
evalAndShow (dynamic_test,[]);
*)
