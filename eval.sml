(* Will Coster *)

(*
 * exp is a datatype encapsulating the abstract syntax of the language e
 *)
datatype exp
  = Var of string
  | Num of int
  | Plus of exp*exp
  | Apply of exp*exp
  | Let of string*exp*exp
  | LetSta of string*string*exp*exp
  | LetDyn of string*string*exp*exp

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
  | FSta of string*exp*exp*((string*enval) list)
  | FDyn of string*exp*exp

(*
 * a datatype for the return value of the eval function.
 * Eval can either return an error message, or a success of a value and a new
 * environment.
 *)
datatype evalret
  = Error of string
  | Success of enval*((string*enval) list)

(*
 * lookup searches an environment (Which is a list of string enval*pairs) for a
 * given identifier.
 * It returns SOME enval if found and NONE if it is not in the environment
 *)
fun lookup (id,[]) = NONE
  | lookup (id,(pid,pval)::ps) = if id=pid then SOME pval else lookup (id, ps)

fun eval (Num (i), p) = Success ((Val i),p)
  | eval (Var (x), p) = (case lookup(x, p) of
    SOME v => Success (v, p)
    | NONE => Error (concat ["Variable `",x,"` is not in the environment"]))
  | eval (Plus (a,b), p) = (case ((eval (a,p)),(eval (b,p))) of
      (*if we have proper values, pull out the ints and add them together*)
      (Success ((Val anum),_), Success ((Val bnum),_)) =>
          Success ((Val (anum+bnum)),p)
      (*
       * If one of the values evaluates to an error, or if there is a type
       * mismatch, report an error
       *)
      | (Error s,_) => Error s
      | (_, Error s) => Error s
      | _ => Error "Type error, plus requires two values.")
  | eval (Apply (fexp,exp), p) = let
      (*
       * a helper function that Wraps two calls to eval, one to set up the local
       * environment, the other to execute the function
       * gp is the environment to return, this stops local variables from
       * bleeding into the global environment
       *)
      fun apply (fexp,pexp,p,gp) = (case eval (pexp,p) of
        Success (_,lp) => (case eval (fexp,lp@p) of 
          Success (v,_) => Success (v,gp)
          | Error s => Error (concat ["Could not evaluate function: ",s]))
        | Error s => Error (concat ["Could not set up local environment: ",s]))
    in
      (*evaluate both sides sides of the apply*)
      case (eval (fexp,p),eval (exp,p)) of
        (*
         * if the function value is is a statif or dynamic function, pull out
         * the relevant bits and pass to apply helper
         *)
        (Success (FSta (fid,fexp,pexp,fp),_), Success (xval,_)) =>
            apply (fexp,pexp,(fid,xval)::fp,p)
        | (Success (FDyn (fid,fexp,pexp),_), Success (xval,_)) =>
            apply (fexp,pexp,(fid,xval)::p,p)
        (*Otherwise report the error that occured*)
        | (Error s,_) => Error s
        | (_,Error s) => Error s
        | _ => Error "Attempt to apply with a non-function value"
    end
    (*first attempt to setup the local environment*)
  | eval (Let (id,exp,inexp), p) = (case eval (exp,p) of 
    (*if successful assign to lp, and evaluate the main expression*)
    Success (v,_) => eval (inexp,(id,exp)::p)
    | Error s => Error s)
  (*
   * The let for functions are fairly straight forward, they just copy the
   * supplied expression and strings into the correct structures.
   *)
  | eval (LetSta (fid,xid,fexp,pexp), p) = let
      val f = FSta (xid,fexp,pexp,p)
    in
      Success (f,(fid,f)::p)
    end
  | eval (LetDyn (fid,xid,fexp,pexp), p) = let
      val f = FDyn (xid,fexp,pexp)
    in
      Success (f,(fid,f)::p)
    end

(*Pretty print functions for enval*)
fun showValue (Success ((Val i),p)) = print ((Int.toString(i))^"\n")
  | showValue (Success ((FSta _),p)) = print ("Static function...\n")
  | showValue (Success ((FDyn _),p)) = print ("Dynamic function...\n")
  | showValue (Error s) = print (s^"\n")

(*evaluate and print an expression*)
fun evalAndShow (exp,p) = let 
    val v = eval (exp,p)
    val _ = showValue (v)
  in
    v
  end;

(*evaluate a list of expressions, and print out the value of each expression*)
fun evalList ([],p) = Error "No expressions given"
  | evalList ([e],p) = evalAndShow (e,p)
  | evalList ((e::es),p) = (case evalAndShow (e,p) of
    Success (v,p) => evalList (es,p)
    | Error s => Error s);

(*

The following is an example that uses all of the features of e, and illustrates
the differences between statically and dynamically bound functions:

let a = 47
letdyn d_add(x) = x + b in let b = a in 0
letsta s_add(x) = x + b in let b = a in 0
d_add(3)
s_add(3)
let a = 42
d_add(3)
s_add(3)
*)

(*
val example = [ Let("a",Num(47),Num(0)),
    LetDyn("d_add","x",Plus(Var("x"),Var("b")),Let("b",Var("a"),Num(0))),
    LetSta("s_add","x",Plus(Var("x"),Var("b")),Let("b",Var("a"),Num(0))),
    Apply(Var("d_add"),Num(3)),
    Apply(Var("s_add"),Num(3)),
    Let("a",Num(42),Num(0)),
    Apply(Var("d_add"),Num(3)),
    Apply(Var("s_add"),Num(3)) ];
evalList (example,[]);
*)

