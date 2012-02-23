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
    | Raw of string

(* A Method is a string name, a list of string*type params, and a list of opcodes *)
  type Method = string*Type*((string*Type) list)*(OP list)
(* An entire program is just a collection of Methods *)
  type Program = Method list

  fun printType pi32 = "i32*"
    | printType i32 = "i32"
    | printType i1 = "i1"
    | printType notype = ""

  fun printArg (Num i) = Int.toString i
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
    | printOP (Raw str) = str

  fun printMethod (name,rtype,args,ops) = let
      val showArgs = foldr (
          fn ((var,ty),rst) => 
            case rst of
            "" => concat [(printType ty), " %", var]
            | _ => concat [rst, ", ", (printType ty), " %", var]
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

end
