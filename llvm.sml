(* Will Coster *)

structure LLVM = 
struct
  datatype Type = notype | pi32  | i32 | i1
  type Result = string
  datatype Arg = 
    Num of int
    | Variable of string
    | Label of string
  datatype OP = 
    DefnLabel of string
    | Alias of Arg*Arg (*Not an actual byte code, but is used in replacing variables with constant expressions*)
    | Load of Result*Type*Arg
    | Store of Type*Arg*Arg
    | Add of Result*Type*Arg*Arg
    | Sub of Result*Type*Arg*Arg
    | Mul of Result*Type*Arg*Arg
    | Div of Result*Type*Arg*Arg
    | CmpEq of Result*Type*Arg*Arg
    | CmpNe of Result*Type*Arg*Arg
    | CmpGt of Result*Type*Arg*Arg
    | CmpGe of Result*Type*Arg*Arg
    | CmpLt of Result*Type*Arg*Arg
    | CmpLe of Result*Type*Arg*Arg
    | Br of Arg
    | CndBr of Arg*Arg*Arg
    | Ret of Type*Arg
    | And of Result*Type*Arg*Arg
    | Or of Result*Type*Arg*Arg
    | Alloca of Result*Type
    | Ashr of Result*Type*Arg*Arg
    | Xor of Result*Type*Arg*Arg
    | Call of Result*Type*string*(Arg list)
    | Print of Result*Arg
    | Raw of string
    | Phi of Result*((Arg*Arg) list) (* Needs to be value/variabe,Label(of the corresponding block) *)

(* A Method is a string name, a list of string*type params, and a list of opcodes *)
  type Method = string*Type*((string*Type) list)*(OP list)
(* An entire program is just a collection of Methods *)
  type Program = Method list

  fun printType pi32 = "i32*"
    | printType i32 = "i32"
    | printType i1 = "i1"
    | printType notype = ""

  fun printArg (Num i) = 
    (*sml formats negative numbers with a ~ instead of a -*)
      if( i >= 0 ) then Int.toString i
      else (concat ["-",(Int.toString (0-i))])
    | printArg (Variable v) = concat ["%",v]
    | printArg (Label v) = concat ["label %",v]

(* Helpers for printing various types of opcodes *)
  val combArgs = foldl (
      fn (a,rst) => 
        case rst of
        "" => a
        | _ => concat [rst, ", ", a]
    ) "";

  fun h_printOP code ty args = concat [code," ",(printType ty)," ",combArgs (map printArg args)]
  fun h_printROP res code ty args = concat ["%",res," = ",(h_printOP code ty args)]

  (*call statements and allocas are never equal because they have side effects each call*)
  fun eqOP (Store (ty_1,a1_1,a2_1)) (Store (ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Add (_,ty_1,a1_1,a2_1)) (Add (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Sub (_,ty_1,a1_1,a2_1)) (Sub (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Mul (_,ty_1,a1_1,a2_1)) (Mul (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Div (_,ty_1,a1_1,a2_1)) (Div (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (And (_,ty_1,a1_1,a2_1)) (And (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Or (_,ty_1,a1_1,a2_1)) (Or (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Xor (_,ty_1,a1_1,a2_1)) (Xor (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (Ashr (_,ty_1,a1_1,a2_1)) (Ashr (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpEq (_,ty_1,a1_1,a2_1)) (CmpEq (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpNe (_,ty_1,a1_1,a2_1)) (CmpNe (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpGt (_,ty_1,a1_1,a2_1)) (CmpGt (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpGe (_,ty_1,a1_1,a2_1)) (CmpGe (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpLt (_,ty_1,a1_1,a2_1)) (CmpLt (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CmpLe (_,ty_1,a1_1,a2_1)) (CmpLe (_,ty_2,a1_2,a2_2)) = (ty_1 = ty_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    | eqOP (CndBr (a1_1,a2_1,a3_1)) (CndBr (a1_2,a2_2,a3_2)) = (a3_1 = a3_2 andalso a1_1 = a1_2 andalso a2_1 = a2_2)
    (*| eqOP (Load (_,ty_1,arg_1)) (Load (_,ty_2,arg_2)) = (ty_1 = ty_2 andalso arg_1 = arg_2)*)
    | eqOP _ _ = false
  fun eqOP' (a,b) = eqOP a b
  
  fun resultOf (Load (res,ty,arg)) = SOME res
    | resultOf (Add (res,ty,a1,a2)) = SOME res
    | resultOf (Sub (res,ty,a1,a2)) = SOME res
    | resultOf (Mul (res,ty,a1,a2)) = SOME res
    | resultOf (Div (res,ty,a1,a2)) = SOME res
    | resultOf (And (res,ty,a1,a2)) = SOME res
    | resultOf (Or (res,ty,a1,a2)) = SOME res
    | resultOf (Xor (res,ty,a1,a2)) = SOME res
    | resultOf (Ashr (res,ty,a1,a2)) = SOME res
    | resultOf (CmpEq (res,ty,a1,a2)) = SOME res
    | resultOf (CmpNe (res,ty,a1,a2)) = SOME res
    | resultOf (CmpGt (res,ty,a1,a2)) = SOME res
    | resultOf (CmpGe (res,ty,a1,a2)) = SOME res
    | resultOf (CmpLt (res,ty,a1,a2)) = SOME res
    | resultOf (CmpLe (res,ty,a1,a2)) = SOME res
    | resultOf (Alloca (res,ty)) = SOME res
    | resultOf (Call (res,ty,name,args)) = SOME res
    | resultOf _ = NONE

  fun replaceVar [] code = code
    | replaceVar ((old,new)::xs) code = let
        fun replArg (Variable v) = if v = old then (Variable new) else (Variable v)
          | replArg arg = arg
        fun replOP (Load (res,ty,a1)) = Load (res,ty,(replArg a1))
          | replOP (Store (ty,a1,a2)) = Store (ty,(replArg a1),(replArg a2))
          | replOP (Add (res,ty,a1,a2)) = Add (res,ty,(replArg a1),(replArg a2))
          | replOP (Sub (res,ty,a1,a2)) = Sub (res,ty,(replArg a1),(replArg a2))
          | replOP (Mul (res,ty,a1,a2)) = Mul (res,ty,(replArg a1),(replArg a2))
          | replOP (Div (res,ty,a1,a2)) = Div (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpEq (res,ty,a1,a2)) = CmpEq (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpNe (res,ty,a1,a2)) = CmpNe (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpGt (res,ty,a1,a2)) = CmpGt (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpGe (res,ty,a1,a2)) = CmpGe (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpLt (res,ty,a1,a2)) = CmpLt (res,ty,(replArg a1),(replArg a2))
          | replOP (CmpLe (res,ty,a1,a2)) = CmpLe (res,ty,(replArg a1),(replArg a2))
          | replOP (CndBr (a1,a2,a3)) = CndBr ((replArg a1),a2,a3)
          | replOP (Ret (ty,a1)) = Ret (ty,(replArg a1))
          | replOP (And (res,ty,a1,a2)) = And (res,ty,(replArg a1),(replArg a2))
          | replOP (Or (res,ty,a1,a2)) = Or (res,ty,(replArg a1),(replArg a2))
          | replOP (Ashr (res,ty,a1,a2)) = Ashr (res,ty,(replArg a1),(replArg a2))
          | replOP (Xor (res,ty,a1,a2)) = Xor (res,ty,(replArg a1),(replArg a2))
          | replOP (Call (res,ty,fname,args)) = Call (res,ty,fname,(map replArg args))
          | replOP (Print (res,arg)) = Print (res,(replArg arg))
          | replOP (Alias (a1,a2)) = Alias ((replArg a1),(replArg a2))
          | replOP code = code
        val new_code = map replOP code
      in replaceVar xs new_code end

  fun printOP (DefnLabel label) =  concat ["\n",label,":"]
    | printOP (Load (res,ty,arg)) =  h_printROP res "load" ty [arg]
    | printOP (Store (ty,a1,a2)) =  concat [(h_printOP "store" ty [a1]),", ",(printType ty),"* ",(printArg a2)]
    | printOP (Add (res,ty,a1,a2)) =  h_printROP res "add" ty [a1, a2]
    | printOP (Sub (res,ty,a1,a2)) =  h_printROP res "sub" ty [a1, a2]
    | printOP (Mul (res,ty,a1,a2)) =  h_printROP res "mul" ty [a1, a2]
    | printOP (Div (res,ty,a1,a2)) =  h_printROP res "sdiv" ty [a1, a2]
    | printOP (And (res,ty,a1,a2)) =  h_printROP res "and" ty [a1, a2]
    | printOP (Or (res,ty,a1,a2)) =  h_printROP res "or" ty [a1, a2]
    | printOP (Xor (res,ty,a1,a2)) =  h_printROP res "xor" ty [a1, a2]
    | printOP (Ashr (res,ty,a1,a2)) =  h_printROP res "ashr" ty [a1, a2]
    | printOP (CmpEq (res,ty,a1,a2)) =  h_printROP res "icmp eq" ty [a1, a2]
    | printOP (CmpNe (res,ty,a1,a2)) =  h_printROP res "icmp ne" ty [a1, a2]
    | printOP (CmpGt (res,ty,a1,a2)) =  h_printROP res "icmp sgt" ty [a1, a2]
    | printOP (CmpGe (res,ty,a1,a2)) =  h_printROP res "icmp sge" ty [a1, a2]
    | printOP (CmpLt (res,ty,a1,a2)) =  h_printROP res "icmp slt" ty [a1, a2]
    | printOP (CmpLe (res,ty,a1,a2)) =  h_printROP res "icmp sle" ty [a1, a2]
    | printOP (CndBr (a1,a2,a3)) =  h_printOP "br" i1 [a1, a2, a3]
    | printOP (Br (a1)) =  h_printOP "br" notype [a1]
    | printOP (Ret (ty,a)) =  h_printOP "ret" ty [a]
    | printOP (Alloca (res,ty)) =  h_printROP res "alloca" ty []
    | printOP (Call (res,ty,name,args)) =  concat [(h_printROP res "call" ty [])," @",name,"(",(combArgs (map (fn x=> concat["i32 ",printArg x]) args)),")"]
    | printOP (Print (res,arg)) = concat["%",res," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 ",(printArg arg),")"]
    | printOP (Raw str) = str
    | printOP (Phi (res,args)) =  concat ["%",res," = phi i32 ",(combArgs (map (fn (x,y) => concat["[ ",printArg x,",",printArg y,"]"]) args))]
    | printOP (Alias (a1,a2)) = concat ["alias ",(printArg a1)," = ",(printArg a2)]

  fun printMethod (name,rtype,args,ops) = let
      val showArgs = foldr (
          fn ((var,ty),rst) => 
            case rst of
            "" => concat [(printType ty), " %", var,"__0"]
            | _ => concat [rst, ", ", (printType ty), " %", var,"__0"]
        ) "";
      val showOps = concat o map (fn x => concat ["\t",(printOP x), "\n"]);
    in
      concat ["define ",(printType rtype)," @",name,"(",(showArgs args),") {\n",(showOps ops),"}\n\n"]
    end

  fun printProgram program = concat [
        "@.str = private constant [4 x i8] c\"%d\\0A\\00\", align 1\n\n"
      , (foldl (fn (a,b) => concat [a,"\n",b]) "" (map printMethod program))
      , "declare i32 @printf(i8*, ...)\n"
    ]

  fun insertAfterLabel code new_code = (case code of
      (DefnLabel l)::rest => ((DefnLabel l)::new_code@rest)
    | _ => new_code@code)

end
