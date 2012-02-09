(* Will Coster *)

(*
 * env is a datatype that covers the possible values that can be stored in the
 * environment
 *)
datatype enval
  = Val of int
  (* Functions contain a parameter identifier, an expression, and some
   * expression for setting local environment
   * static bound also includes a snapshot of the global environment when it
   * was created
   *)
  | FSta of string*exp*((string*enval) list)
  | FDyn of string*exp

(*
 * a datatype for the return value of the eval function.
 * Eval can either return an error message, or a success of a value and a new
 * environment.
 *)
datatype evalret
  = Error of string
  | Success of enval

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
  | eval (Apply (fexp,exp), p) = 
    (*evaluate both sides sides of the apply*)
    (case (eval (fexp,p),eval (exp,p)) of
      (*
       * if the function value is is a statif or dynamic function, pull out
       * the relevant bits and pass to apply helper
       *)
      (Success (FSta (fid,fexp,fp)), Success xval) =>
          eval (fexp,(fid,xval)::fp)
      | (Success (FDyn (fid,fexp)), Success xval) =>
          eval (fexp,(fid,xval)::p)
      (*Otherwise report the error that occured*)
      | (Error s,_) => Error s
      | (_,Error s) => Error s
      | _ => Error "Attempt to apply with a non-function value")
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

(*Pretty print functions for enval*)
fun showValue (Success (Val i)) = print ((Int.toString(i))^"\n")
  | showValue (Success (FSta _)) = print ("Static function...\n")
  | showValue (Success (FDyn _)) = print ("Dynamic function...\n")
  | showValue (Error s) = print (s^"\n")

(*evaluate and print an expression*)
fun evalAndShow x = showValue (eval x)

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
