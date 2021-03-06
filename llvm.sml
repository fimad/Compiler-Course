(* Will Coster *)

structure LLVM = 
struct
  datatype Type
    = notype
    | usertype of string 
    | i1
    | i8
    | i32
    | float
    | array of Type
    | vector of int*Type
    | ptr of Type
    | usertype_form of string*string (*used in intermediate operations when dealing with forms*)
    | usertype_parent
  type UserType = string*((string*(Type list)) list)(*type name, forms*) (*forms = (form name, types in form)*)
  type Result = string
  datatype Arg = 
    Int of int
    | Bool of int
    | Float of real
    | Variable of string
    | Label of string
    | Undef
  datatype OP = 
    DefnLabel of string
    | ZExt of Result*Type*Arg*Type
    | SiToFp of Result*Type*Arg*Type
    | Bitcast of Result*Type*Arg*Type
    | Alias of Arg*Arg (*Not an actual byte code, but is used in replacing variables with constant expressions*)
    | Load of Result*Type*Arg
    | Store of Type*Arg*Arg
    | GetElementPtr of Result*Type*Arg*(Arg list)
    | ExtractElement of Result*Type*Arg*Arg
    | InsertElement of Result*Type*Arg*Type*Arg*Arg
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
    | Alloca of Result*Type*int
    | Ashr of Result*Type*Arg*Arg
    | Xor of Result*Type*Arg*Arg
    | Call of Result*Type*string*((Arg*Type) list)
    | TailCall of Result*Type*string*((Arg*Type) list)
    | Print of Result*Type*Arg
    | TailPrint of Result*Type*Arg
    | Raw of string
    | Phi of Result*((Arg*Arg) list) (* Needs to be value/variabe,Label(of the corresponding block) *)

(* A Method is a string name, a list of string*type params, and a list of opcodes *)
  type Method = string*Type*((string*Type) list)*(OP list)
(* An entire program is just a collection of Methods *)
  type Program = Method list

  fun isPrimitive i32 = true
    | isPrimitive i8 = true
    | isPrimitive i1 = true
    | isPrimitive float = true
    | isPrimitive (ptr _) = true (*pointers are primitives?*)
    | isPrimitive _ = false

  (*hacks for user types*)
  exception LLVMError of string;
  val userTypeScope = ref []
  fun addUserType ut = userTypeScope := ut::(!userTypeScope)
  fun isUserType name = List.exists (fn (name',_) => name = name') (!userTypeScope)
  fun isUserTypeForm form = List.exists (fn (_,forms) => List.exists (fn (form',_) => form = form') forms) (!userTypeScope)
  fun getUserType name = (case (List.filter (fn (name',_) => name = name') (!userTypeScope)) of
    [] => raise (LLVMError (concat ["User type '",name,"' does not exist!"]))
    | (x::_) => x)
  fun getTypeForForm form = (case (List.filter (fn (_,forms) => List.exists (fn (f,_) => f=form) forms) (!userTypeScope)) of
    [] => raise (LLVMError (concat ["No user type has the form '",form,"'!"]))
    | ((name,_)::_) => usertype name)
  fun getUserTypeForForm form = let
      val (usertype name) = getTypeForForm form
    in getUserType name end
  fun getFormTypes form = (case (List.filter (fn (f,_) => f=form) (#2 ((getUserTypeForForm) form))) of
    [] => raise (LLVMError (concat ["No user type has the form '",form,"'!"]))
    | ((_,types)::_) => types)
  fun getFormIndex form = let
      fun getIndex i ((f,_)::fs) = if form = f then i else getIndex (i+1) fs (*should throw error before it reaches end of list*)
      val (_,forms) = (getUserTypeForForm) form
    in getIndex 0 forms end
  fun getIndexForForm name i = let
      val (name,forms) = getUserType name
      val _ = if length forms < i then raise (LLVMError "Index is TOO HIGH! should never happen though...") else ()
    in
      List.nth (forms,i)
    end
  fun isFormOfUserType form name = let
      val (_,forms) = getUserType name
    in
      List.exists (fn (form',_) => form' = form) forms
    end

  fun sizeOfType i32 = 4
    | sizeOfType i8 = 1
    | sizeOfType i1 = 1
    | sizeOfType (ptr _) = 8
    | sizeOfType float = 8
    | sizeOfType (array (ty)) = 8 (* arrays are just pointers yo! *)
    | sizeOfType (usertype name) = let
        val (ut,forms) = getUserType name
        val sizes = (map (fn (_,ts) => foldr (op +) 0 (map sizeOfType (map (fn t => if isPrimitive t then t else ptr t) ts))) forms)
        val maxSize = foldr Int.max 0 sizes
      in
        maxSize + 4 (* the 4 is for the form int *)
      end

  fun printType i32 = "i32"
    | printType i8 = "i8"
    | printType i1 = "i1"
    | printType float = "double"
    | printType usertype_parent = "%T"
    | printType (ptr ty) = concat [printType ty,"*"]
    | printType (array ty) = "%A*"
    | printType (vector (d,ty)) = concat ["<",Int.toString d," x ",printType ty,">"]
    (*| printType (array (size,ty)) = concat ["[",(Int.toString size)," x ",(printType ty),"]"]*)
    | printType (usertype _) = printType (ptr i8)
    | printType (usertype_form (name,form)) = concat ["%T.",name,".",form]
    | printType notype = ""

  fun printUserType (name,forms) = let
      fun printTypes [] = []
        | printTypes [t] = [printType t]
        | printTypes (t::ts) = (printType t)::","::(printTypes ts)
      fun printForm name (form,types) = 
        concat (["%T.",name,".",form," = type {"]@(printTypes types)@["}\n"])
    in
      concat (map (printForm name) forms)
    end

  fun arrayType (array (array sub)) = arrayType (array sub)
    | arrayType (array (ty)) = SOME ty
    | arrayType _ = NONE

  fun printPosReal exp f =
      if f >= 10.0 then printPosReal (exp+1) (f/10.0)
      else if f < 1.0 then printPosReal (exp-1) (f*10.0)
      else concat [Real.toString f,if(Real.== (#whole (Real.split f),f)) then ".0" else "","e",printArg (Int exp)]

  and printArg (Int i) = 
    (*sml formats negative numbers with a ~ instead of a -*)
      if( i >= 0 ) then Int.toString i
      else (concat ["-",(Int.toString (0-i))])
    | printArg (Float f) = 
    (*sml formats negative numbers with a ~ instead of a -*)
      if( f >= 0.0 ) then printPosReal 0 f
      else (concat ["-",(printPosReal 0 (0.0-f))])
    | printArg (Bool 0) = "0"
    | printArg (Bool _) = "1"
    | printArg (Variable v) = concat ["%",v]
    | printArg (Label v) = concat ["label %",v]
    | printArg (Undef) = "undef"

(* Helpers for printing various types of opcodes *)
  val combArgs = foldl (
      fn (a,rst) => 
        case rst of
        "" => a
        | _ => concat [rst, ", ", a]
    ) "";

  fun h_printOP code ty args = concat [code," ",(printType ty)," ",combArgs (map printArg args)]
  fun h_printROP res code ty args = concat ["%",res," = ",(h_printOP code ty args)]

  (*
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
  *)
  
  fun resultOf (Load (res,ty,arg)) = SOME res
    | resultOf (ZExt (res,_,_,_)) = SOME res
    | resultOf (SiToFp (res,_,_,_)) = SOME res
    | resultOf (Bitcast (res,_,_,_)) = SOME res
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
    | resultOf (Alloca (res,ty,num)) = SOME res
    | resultOf (GetElementPtr (res,ty,_,_)) = SOME res
    | resultOf (ExtractElement (res,ty,_,_)) = SOME res
    | resultOf (InsertElement (res,ty,_,_,_,_)) = SOME res
    | resultOf (Call (res,ty,name,args)) = SOME res
    | resultOf (TailCall (res,ty,name,args)) = SOME res
    | resultOf _ = NONE

  fun replaceVar [] code = code
    | replaceVar ((old,new)::xs) code = let
        fun replArg (Variable v) = if v = old then (Variable new) else (Variable v)
          | replArg arg = arg
        fun replOP (Load (res,ty,a1)) = Load (res,ty,(replArg a1))
          | replOP (ZExt (res,ty1,a1,ty2)) = ZExt (res,ty1,(replArg a1),ty2)
          | replOP (SiToFp (res,ty1,a1,ty2)) = SiToFp (res,ty1,(replArg a1),ty2)
          | replOP (Bitcast (res,ty1,a1,ty2)) = Bitcast (res,ty1,(replArg a1),ty2)
          | replOP (Store (ty,a1,a2)) = Store (ty,(replArg a1),(replArg a2))
          | replOP (GetElementPtr (res,ty1,a1,args)) = GetElementPtr (res,ty1,(replArg a1),(map replArg args))
          | replOP (ExtractElement (res,ty1,a1,args)) = ExtractElement (res,ty1,(replArg a1),(replArg args))
          | replOP (InsertElement (res,ty1,a1,ty2,a2,a3)) = InsertElement (res,ty1,(replArg a1),ty2,(replArg a2),(replArg a3))
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
          | replOP (Call (res,ty,fname,args)) = Call (res,ty,fname,(map (fn (r,t) => (replArg r,t)) args))
          | replOP (TailCall (res,ty,fname,args)) = TailCall (res,ty,fname,(map (fn (r,t) => (replArg r,t)) args))
          | replOP (Print (res,t,arg)) = Print (res,t,(replArg arg))
          | replOP (TailPrint (res,t,arg)) = TailPrint (res,t,(replArg arg))
          | replOP (Alias (a1,a2)) = Alias ((replArg a1),(replArg a2))
          | replOP code = code
        val new_code = map replOP code
      in replaceVar xs new_code end

  fun printOP (DefnLabel label) =  concat ["\n",label,":"]
    | printOP (ZExt (res,ty1,arg,ty2)) =  concat [h_printROP res "zext" ty1 [arg]," to ",printType ty2]
    (*| printOP (ZExt (res,ty1,arg,ty2)) =  concat [h_printROP res "zext" notype [], printType ty1," ", printArg arg," to ",printType ty2]*)
    | printOP (SiToFp (res,ty1,arg,ty2)) =  concat [h_printROP res "sitofp" ty1 [arg]," to ",printType ty2]
    | printOP (Bitcast (res,ty1,arg,ty2)) =  concat [h_printROP res "bitcast" ty1 [arg]," to ",printType ty2]
    | printOP (Load (res,ty,arg)) =  h_printROP res "load" ty [arg]
    (*| printOP (GetElementPtr (res,ty1,a1,a2)) = concat ["%",res," = getelementptr inbounds ",(printType ty1)," ",(printArg a1),", i32 0",", i32 ",(printArg a2)]*)
    | printOP (GetElementPtr (res,ty,a1,args)) = concat ["%",res," = getelementptr ",(printType ty)," ",(printArg a1),concat (map (fn a=>concat[", i32 ",printArg a]) args)]
    | printOP (ExtractElement (res,ty,a1,a2)) = concat ["%",res," = extractelement ",(printType ty)," ",(printArg a1),", i32 ", printArg a2]
    | printOP (InsertElement (res,ty1,a1,ty2,a2,a3)) = concat ["%",res," = insertelement ",(printType ty1)," ",(printArg a1),", ",printType ty2," ",printArg a2,", i32 ", printArg a3]
    | printOP (Store (ty,a1,a2)) =  concat [(h_printOP "store" ty [a1]),", ",(printType ty),"* ",(printArg a2)]
    | printOP (Add (res,float,a1,a2)) =  h_printROP res "fadd" float [a1, a2]
    | printOP (Add (res,v as vector (_,float),a1,a2)) =  h_printROP res "fadd" v [a1, a2]
    | printOP (Add (res,ty,a1,a2)) =  h_printROP res "add" ty [a1, a2]
    | printOP (Sub (res,float,a1,a2)) =  h_printROP res "fsub" float [a1, a2]
    | printOP (Sub (res,v as vector (_,float),a1,a2)) =  h_printROP res "fsub" v [a1, a2]
    | printOP (Sub (res,ty,a1,a2)) =  h_printROP res "sub" ty [a1, a2]
    | printOP (Mul (res,float,a1,a2)) =  h_printROP res "fmul" float [a1, a2]
    | printOP (Mul (res,v as vector (_,float),a1,a2)) =  h_printROP res "fmul" v [a1, a2]
    | printOP (Mul (res,ty,a1,a2)) =  h_printROP res "mul" ty [a1, a2]
    | printOP (Div (res,float,a1,a2)) =  h_printROP res "fdiv" float [a1, a2]
    | printOP (Div (res,v as vector (_,float),a1,a2)) =  h_printROP res "fdiv" v [a1, a2]
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
    | printOP (Alloca (res,ty,num)) =  concat [h_printROP res "alloca" ty [], ", ", printType i32," ",(Int.toString num)]
    | printOP (Call (res,ty,name,args)) =  concat [(h_printROP res "call" ty [])," @",name,"(",(combArgs (map (fn (x,t)=> concat[printType t," ",printArg x]) args)),")"]
    | printOP (TailCall (res,ty,name,args)) =  concat [(h_printROP res "tail call" ty [])," @",name,"(",(combArgs (map (fn (x,t)=> concat[printType t," ",printArg x]) args)),")"]
    | printOP (Print (res,i32,arg)) = concat["%",res," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_int_str, i32 0, i32 0), i32 ",(printArg arg),")"]
    | printOP (Print (res,i1,arg)) = concat["%",res," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_int_str, i32 0, i32 0), i1 ",(printArg arg),")"]
    | printOP (Print (res,float,arg)) = concat["%",res," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_float_str, i32 0, i32 0), double ",(printArg arg),")"]
    | printOP (TailPrint (res,i32,arg)) = concat["%",res," = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_int_str, i32 0, i32 0), i32 ",(printArg arg),")"]
    | printOP (TailPrint (res,i1,arg)) = concat["%",res," = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_int_str, i32 0, i32 0), i1 ",(printArg arg),")"]
    | printOP (TailPrint (res,float,arg)) = concat["%",res," = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.print_float_str, i32 0, i32 0), double ",(printArg arg),")"]
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
        "%T = type { i32, i8 }\n" (* for user types *)
      , "%A = type { i32, i8 }\n" (* for arrays *)
      , concat (map printUserType (!userTypeScope))
      , "\n"
      , "@.print_int_str = private constant [4 x i8] c\"%d\\0A\\00\", align 1\n"
      , "@.print_float_str = private constant [4 x i8] c\"%f\\0A\\00\", align 1\n\n"
      , (foldl (fn (a,b) => concat [a,"\n",b]) "" (map printMethod program))
      , "declare i32 @printf(i8*, ...)\n"
      , "declare noalias i8* @malloc(i32) nounwind\n"
      , "declare void @free(i8*) nounwind\n"
      , "declare i32 @rand() nounwind\n"
    ]

  fun insertAfterLabel code new_code = (case code of
      (DefnLabel l)::rest => ((DefnLabel l)::new_code@rest)
    | _ => new_code@code)

  
(*this should also replace inside the alias list incase there are aliases of aliases*)
fun replaceAlias (a,v) [] = []
  | replaceAlias (a as (Variable a_str),v) ((a',v' as (Variable v'_str))::xs) = (if (v'_str=a_str) then (a',v) else (a',v'))::(replaceAlias (a,v) xs)
  | replaceAlias (a,v) (x::xs) = x::(replaceAlias (a,v) xs)

(* replaces a specific Arg if it is an alias with it's value *)
fun replaceArg [] arg = arg
  | replaceArg ((a as (Variable a_str),new_v)::xs) (arg as (Variable arg_str)) = if arg_str = a_str then new_v else replaceArg (replaceAlias (a,new_v) xs) arg
  | replaceArg _ (arg) = arg
  (*
  | replaceArg ((a,new_v)::xs) (arg as (Variable v)) = if v = a then new_v else replaceArg (replaceAlias (a,new_v) xs) arg
  | replaceArg ((a,(new_v as (Label new_v_str)))::xs) (arg as (Label v)) = if v = a then new_v else replaceArg (replaceAlias (a,new_v) xs) arg
  | replaceArg ((a,(new_v as (Variable new_v_str)))::xs) (arg as (Label v)) = if v = a then (Label new_v_str) else replaceArg (replaceAlias (a,new_v) xs) arg
  | replaceArg (_::xs) arg = replaceArg xs arg
  *)

(* replaces arguments in opcodes if they have been aliased *)
fun replaceInOp aliases code =  let
    val replaceArg = replaceArg aliases (*presupply the list of aliases*)
    fun replaceInOp' (Load (r,t,a1)) = Load (r,t,replaceArg a1)
      | replaceInOp' (Store (t,a1,a2)) = Store (t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (ZExt (res,t1,a1,t2)) = ZExt (res,t1,(replaceArg a1),t2)
      | replaceInOp' (SiToFp (res,t1,a1,t2)) = SiToFp (res,t1,(replaceArg a1),t2)
      | replaceInOp' (Bitcast (res,t1,a1,t2)) = Bitcast (res,t1,(replaceArg a1),t2)
      | replaceInOp' (GetElementPtr (r,t1,a1,args)) = GetElementPtr (r,t1,(replaceArg a1),(map replaceArg args))
      | replaceInOp' (Add (r,t,a1,a2)) = Add (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Sub (r,t,a1,a2)) = Sub (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Mul (r,t,a1,a2)) = Mul (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Div (r,t,a1,a2)) = Div (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpEq (r,t,a1,a2)) = CmpEq (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpNe (r,t,a1,a2)) = CmpNe (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpGt (r,t,a1,a2)) = CmpGt (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpGe (r,t,a1,a2)) = CmpGe (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpLt (r,t,a1,a2)) = CmpLt (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (CmpLe (r,t,a1,a2)) = CmpLe (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Br (a1)) = Br (replaceArg a1)
      | replaceInOp' (CndBr (a1,a2,a3)) = CndBr ((replaceArg a1),(replaceArg a2),(replaceArg a3))
      | replaceInOp' (Ret (t,a1)) = Ret (t,(replaceArg a1))
      | replaceInOp' (And (r,t,a1,a2)) = And (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Or (r,t,a1,a2)) = Or (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Ashr (r,t,a1,a2)) = Ashr (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Xor (r,t,a1,a2)) = Xor (r,t,(replaceArg a1),(replaceArg a2))
      | replaceInOp' (Print (r,t,a1)) = Print (r,t,(replaceArg a1))
      | replaceInOp' (TailPrint (r,t,a1)) = TailPrint (r,t,(replaceArg a1))
      | replaceInOp' (Call (r,t,func,args)) = Call (r,t,func,(map (fn (r,t) => (replaceArg r,t)) args))
      | replaceInOp' (TailCall (r,t,func,args)) = TailCall (r,t,func,(map (fn (r,t) => (replaceArg r,t)) args))
      | replaceInOp' (Phi (r,args)) = Phi (r,(map (fn (v,l)=>((replaceArg v),l)) args))
      | replaceInOp' x = x
    in replaceInOp' code end

end
