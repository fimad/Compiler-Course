(* Will Coster *)

structure LLVM_Translate = 
struct

  type Scope = string*LLVM.Type

  val curlabel = ref 1
  fun nextvar () = concat ["_",Int.toString(!curlabel)]
  fun makenextvar () = let
      val label = nextvar ()
      val _ = (curlabel := !curlabel+1)
    in label end
  fun nextlabel () = concat ["L",Int.toString(!curlabel)]
  fun makenextlabel () = let
      val label = nextlabel ()
      val _ = (curlabel := !curlabel+1)
    in label end

  val methods = ref []
  fun addMethod method = let
    val _ = (methods := method::(!methods))
  in
    method
  end

  (* options for tuning the translator *)
  val config_unroll = ref NONE
  fun setUnrollAmount amt = (config_unroll := amt)
  val config_vectorize = ref false
  fun setVectorize v = (config_vectorize := v)

  fun getProgram () = !methods

  exception TranslationError of string;

  fun setResult newRes (oldRes,code) = let
      fun setResult_help [] = []
        | setResult_help (x::[]) = 
          [(case x of
              (LLVM.Load (_,a1,a2)) => LLVM.Load (newRes,a1,a2)
            | (LLVM.Add (_,a1,a2,a3)) => LLVM.Add (newRes,a1,a2,a3)
            | (LLVM.Sub (_,a1,a2,a3)) => LLVM.Sub (newRes,a1,a2,a3)
            | (LLVM.Mul (_,a1,a2,a3)) => LLVM.Mul (newRes,a1,a2,a3)
            | (LLVM.Div (_,a1,a2,a3)) => LLVM.Div (newRes,a1,a2,a3)
            | (LLVM.CmpEq (_,a1,a2,a3)) => LLVM.CmpEq (newRes,a1,a2,a3)
            | (LLVM.CmpNe (_,a1,a2,a3)) => LLVM.CmpNe (newRes,a1,a2,a3)
            | (LLVM.CmpGt (_,a1,a2,a3)) => LLVM.CmpGt (newRes,a1,a2,a3)
            | (LLVM.CmpGe (_,a1,a2,a3)) => LLVM.CmpGe (newRes,a1,a2,a3)
            | (LLVM.CmpLt (_,a1,a2,a3)) => LLVM.CmpLt (newRes,a1,a2,a3)
            | (LLVM.CmpLe (_,a1,a2,a3)) => LLVM.CmpLe (newRes,a1,a2,a3)
            | (LLVM.And (_,a1,a2,a3)) => LLVM.And (newRes,a1,a2,a3)
            | (LLVM.Or (_,a1,a2,a3)) => LLVM.Or (newRes,a1,a2,a3)
            | (LLVM.Alloca (_,a1,num)) => LLVM.Alloca (newRes,a1,num)
            | (LLVM.Ashr (_,a1,a2,a3)) => LLVM.Ashr (newRes,a1,a2,a3)
            | (LLVM.Xor (_,a1,a2,a3)) => LLVM.Xor (newRes,a1,a2,a3)
            | (LLVM.Call (_,a1,a2,a3)) => LLVM.Call (newRes,a1,a2,a3)
            | (LLVM.Phi (_,a1)) => LLVM.Phi (newRes,a1)
            | (LLVM.Alias (_,a)) => LLVM.Alias ((LLVM.Variable newRes),a)
            | (LLVM.ZExt (_,t1,a,t2)) => LLVM.ZExt (newRes,t1,a,t2)
            | (LLVM.SiToFp (_,t1,a,t2)) => LLVM.SiToFp (newRes,t1,a,t2)
            | (LLVM.Bitcast (_,t1,a,t2)) => LLVM.Bitcast (newRes,t1,a,t2)
            | (LLVM.GetElementPtr (_,t,a1,a2)) => LLVM.GetElementPtr (newRes,t,a1,a2)
            | (LLVM.Print (_,t,a)) => LLVM.Print (newRes,t,a)
            | any => any)]
        | setResult_help (x::xs) = x::(setResult_help xs)
    in
      (newRes, setResult_help code)
      (*(newRes,code@[LLVM.Alias(LLVM.Variable newRes,oldRes)])*)
    end

  fun evalArg scope _ (Ast.Int i) = ([],(LLVM.Int i),LLVM.i32)
    | evalArg scope _ (Ast.Float f) = ([],(LLVM.Float f),LLVM.float)
    | evalArg scope _ (Ast.Bool b) = ([],(LLVM.Bool b),LLVM.i1)
    | evalArg scope fscope expr = let
        val (res,ty,code) = translate expr scope fscope
      in
        (code, (LLVM.Variable res), ty)
      end

  (*takes a list of variables and types, and returns code for casting (can resuse names, they will get renamed later), and final type*)

  and highestType acc [] = acc
    | highestType acc ((x,ty)::xs) =
      if acc = LLVM.float orelse ty = LLVM.float then highestType LLVM.float xs
      else if acc = LLVM.i32 orelse ty = LLVM.i32 then highestType LLVM.i32 xs
      else if acc = LLVM.i1 orelse ty = LLVM.i1 then highestType LLVM.i32 xs
      else if acc = ty then highestType acc xs
      else raise (TranslationError "Only primitive types may be mixed.")
  and highestType' ((x,ty)::xs) = highestType ty xs

  and resolveType' code ty [] = (code,ty)
    | resolveType' code ty ((x',ty')::xs) =
        if ty = ty' then resolveType' code ty xs
        else if ty' = LLVM.i32 then (*raise int one level and try again*)
          resolveType' (code@[LLVM.SiToFp (x',LLVM.i32,LLVM.Variable x',LLVM.float)]) ty ((x',LLVM.float)::xs)
        else if ty' = LLVM.i1 then (*raise bool one level and try again*)
          resolveType' (code@[LLVM.ZExt (x',LLVM.i1,LLVM.Variable x',LLVM.i32)]) ty ((x',LLVM.i32)::xs)
        else raise (TranslationError "Unable to raise type...That should not happen")

  and resolveType [] = raise (TranslationError "Expected Type but none found...")
    | resolveType (xs as ((_,ty)::_)) = resolveType' [] (highestType ty xs) xs

  and ensureVar' code vars [] = (code,vars)
    | ensureVar' code vars ((LLVM.Variable v)::xs) = ensureVar' code (v::vars) xs
    | ensureVar' code vars ((LLVM.Label l)::xs) = ensureVar' code (l::vars) xs
    | ensureVar' code vars (x::xs) = let
        val v = makenextvar ()
      in ensureVar' (code@[LLVM.Alias (LLVM.Variable v,x)]) (v::vars) xs end
  and ensureVars xs = ensureVar' [] [] (rev xs)


  and ensureType ty [] = ()
    | ensureType ty (ty'::tys) =
      if ty <> ty' then raise (TranslationError "WRONG TYPE YO!")
      else ensureType ty tys

  and getTypeForVar [] var = raise (TranslationError (concat ["Unbound variable '",var,"'"]))
    | getTypeForVar ((x,t)::scope) var = if x = var then t else getTypeForVar scope var

    (*
  and getLLVMTypeForVar scope var = let
      fun type2llvm Int =  LLVM.i32
        | type2llvm (Array []) = LLVM.i32
        | type2llvm (Array (d::dims)) = LLVM.array (d,(type2llvm (Array dims)))
    in type2llvm (getTypeForVar scope var) end
    *)

  and llvmTypeForDim ty [] = ty
    | llvmTypeForDim ty (d::im) = LLVM.array (llvmTypeForDim ty im)

  and arrayBaseType (LLVM.array (sub)) = arrayBaseType sub
    | arrayBaseType ty = ty

  and calculateElemPtr var_array ty_array arg_index = let
      val var_elems_ptr = makenextvar()
      val var_elem_ptr = makenextvar()
      val (LLVM.array ty_base) = ty_array
      val code = [
          LLVM.GetElementPtr (var_elems_ptr, ty_array, LLVM.Variable var_array,[LLVM.Int 0,LLVM.Int 1])
        , LLVM.Bitcast (var_elems_ptr,LLVM.ptr LLVM.i8,LLVM.Variable var_elems_ptr,LLVM.ptr ty_base)
        , LLVM.GetElementPtr (var_elem_ptr, LLVM.ptr ty_base, LLVM.Variable var_elems_ptr, [arg_index])
      ]
    in
      (var_elem_ptr,LLVM.ptr ty_base,code)
    end

  and arrayDimFromExps exps scope fscope = let
      val first = length exps
    in
        first
    end

  (*Hack to set variables correctly*)
  and setVariable result exp scope fscope = 
    (case exp of
      (*needed for assign and let*)
      (* (Ast.Var x) => (result, [LLVM.Add (result,LLVM.i32, (LLVM.Num 0), (LLVM.Variable x))]) *)
        (Ast.Var x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Variable x))])
      | (Ast.Int x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Int x))])
      | (Ast.Float x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Float x))])
      | (Ast.Bool x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Bool x))])
      (*needed for everything eles*)
      | exp => let
          val (res,ty,code) = translate exp scope fscope
        in
          setResult result (LLVM.Variable res,code)
        end)

  and typeForFunc id [] = raise (TranslationError (concat ["Function '",id,"' not defined"]))
    | typeForFunc id ((id',ty)::ids) = if id = id' then ty else typeForFunc id ids

  and translate (Ast.Print ast) scope fscope = let
      val pres = makenextvar ()
      val (code,res,ty) = evalArg scope fscope ast
    in
      (pres,LLVM.i32,code@[LLVM.Print (pres,ty,res)])
    end
  | translate (Ast.Dim (exp)) scope fscope = let
      val var_size  = makenextvar ()
      val (exp_code,exp_res,exp_ty) = evalArg scope fscope exp
      val _ = case exp_ty of LLVM.array _ => () | _ => raise (TranslationError "Attempt to get dimension of non array")
      val code = exp_code@[
          LLVM.GetElementPtr (var_size, exp_ty, exp_res, [LLVM.Int 0, LLVM.Int 0])
        , LLVM.Load (var_size, LLVM.ptr LLVM.i32, LLVM.Variable var_size)
      ]
    in
        (var_size,LLVM.i32,code)
    end
  | translate (Ast.Block asts) scope fscope = let
      val i = makenextvar ()
    in
      foldl (fn (exp,(_,_,prev_code)) => let
              val (res,ty,code) = translate exp scope fscope
            in
              (res,ty,prev_code@code)
            end
            ) (i,LLVM.i32,[LLVM.Alias (LLVM.Variable i,LLVM.Int 0)]) asts
    end
  | translate (Ast.Int (i)) scope fscope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Int i))]
    in (l,LLVM.i32,code) end
  | translate (Ast.Float (i)) scope fscope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Float i))]
    in (l,LLVM.float,code) end
  | translate (Ast.Bool (i)) scope fscope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Bool i))]
    in (l,LLVM.i1,code) end
  | translate (Ast.Array (exps)) scope fscope =  let
      val new_res = makenextvar ()
      (* Find the highest type in expressions *)
      val ((_,e_ty)::types) = map (fn e => let val (r,t,_) = translate e scope fscope in (r,t) end) exps
      val high_type = highestType e_ty types

      val (res,res_ty,create_code) = translate (Ast.EmptyArray (high_type,length exps)) scope fscope

      val (_,update_code) = foldl (fn (e,(i,prev_code)) => let
              val (ptr,ty,ptr_code) = calculateElemPtr res res_ty (LLVM.Int i)
              val (exp_code,exp_res,exp_ty) = evalArg scope fscope e
              val (alias_code,[var]) = ensureVars [exp_res]
              val (exp_cast,exp_ty) = resolveType' [] high_type [(var,exp_ty)]
            in
              (i+1,prev_code@ptr_code@exp_code@alias_code@exp_cast@[LLVM.Store (high_type,LLVM.Variable var,LLVM.Variable ptr)])
            end
          ) (0,[]) exps
    in
      (new_res,res_ty,create_code@update_code@[LLVM.Alias (LLVM.Variable new_res,LLVM.Variable res)])
    end
  | translate (Ast.EmptyArray (pty,dim)) scope fscope =  let
      val var_malloc = makenextvar ()
      val var_array = makenextvar ()
      val var_size_ptr = makenextvar ()
      val var_res = makenextvar ()
      val ty = LLVM.array pty
      val code = [
          LLVM.Call (var_malloc,LLVM.ptr LLVM.i8,"malloc",[(LLVM.Int (8+(LLVM.sizeOfType ty)*dim),LLVM.i32)]) (*the extra 4 is for size info*)
        , LLVM.Bitcast (var_array,LLVM.ptr LLVM.i8,LLVM.Variable var_malloc,ty)
        , LLVM.GetElementPtr (var_size_ptr, ty, LLVM.Variable var_array, [LLVM.Int 0, LLVM.Int 0])
        , LLVM.Store (LLVM.i32, LLVM.Int dim, LLVM.Variable var_size_ptr)
        , LLVM.Alias (LLVM.Variable var_res,LLVM.Variable var_array)
      ]
    in
      (var_res,ty,code)
    end
  | translate (Ast.ArrayIndex (exp,index)) scope fscope = let
        val (exp_code,exp_res,exp_ty) = evalArg scope fscope exp
        val (i_code,i_res,i_ty) = evalArg scope fscope index

        (* error checking *)
        val base_ty = case exp_ty of LLVM.array t => t | _ => raise (TranslationError "Can only index arrays!!!")
        val _ = case i_ty of LLVM.i32 => () | _ => raise (TranslationError "Index of an array must be an int!")

        val (alias_code,[var]) = ensureVars [exp_res]
        val (ptr_res,ptr_ty,ptr_code) = calculateElemPtr var exp_ty i_res
        val var_res = makenextvar ()

        val code = exp_code@i_code@alias_code@ptr_code@[
            LLVM.Load (var_res,ptr_ty,LLVM.Variable ptr_res)
        ]
      in
        (var_res,base_ty,code)
      end
  | translate (Ast.Var (x)) scope fscope =  let
      val ty = getTypeForVar scope x
      val code = []
    in
      (x,ty,code)
    end
  | translate (Ast.NotEq (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpNe (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.And (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val _ = ensureType LLVM.i1 [ty1,ty2]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@[LLVM.And (l,LLVM.i1,arg1,arg2)])
    end
  | translate (Ast.Or (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val _ = ensureType LLVM.i1 [ty1,ty2]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@[LLVM.Or (l,LLVM.i1,arg1,arg2)])
    end
  | translate (Ast.Eq (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpEq (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Less (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpLt (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.LessEq (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpLe (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.More (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpGt (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.MoreEq (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@code2@alias_code@cast_code@[LLVM.CmpGe (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Not (a)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val _ = ensureType LLVM.i1 [ty1]
      val l = makenextvar ()
    in
      (l,LLVM.i1,code1@[LLVM.Xor (l,LLVM.i1,(LLVM.Int 1),arg1)])
    end
  | translate (Ast.Plus (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,ty,code1@code2@alias_code@cast_code@[LLVM.Add (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Minus (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,ty,code1@code2@alias_code@cast_code@[LLVM.Sub (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Mult (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a 
      val (code2,arg2,ty2) = evalArg scope fscope b 
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,ty,code1@code2@alias_code@cast_code@[LLVM.Mul (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Div (a,b)) scope fscope = let
      val (code1,arg1,ty1) = evalArg scope fscope a
      val (code2,arg2,ty2) = evalArg scope fscope b
      val (alias_code,[var1,var2]) = ensureVars [arg1,arg2]
      val (cast_code,ty) = resolveType [(var1,ty1),(var2,ty2)]
      val l = makenextvar ()
    in
      (l,ty,code1@code2@alias_code@cast_code@[LLVM.Div (l,ty,LLVM.Variable var1,LLVM.Variable var2)])
    end
  | translate (Ast.Apply ((Ast.Var v),exps)) scope fscope = 
    if LLVM.isUserTypeForm v then
      let
        val form = v

        val var_malloc = makenextvar ()
        val var_form_type = makenextvar ()
        val var_T_type = makenextvar ()
        val var_form_ptr = makenextvar ()
        val var_result = makenextvar ()

        val (user_type as (LLVM.usertype name)) = LLVM.getTypeForForm form
        val form_type = LLVM.usertype_form (name,form)
        val types = LLVM.getFormTypes form
        (* error checking, wut?*)
        val _ = if length types <> length exps then raise (TranslationError (concat["Incorrect number of expressions for '",form,"'"])) else ()

        fun initialize i [] = []
          | initialize i ((t,exp)::xs) = let
              val (code,arg,ety) = evalArg scope fscope exp
              val (alias_code,[var]) = ensureVars [arg]
              val (cast_code,ty) = resolveType' [] t [(var,ety)]
              val var_val_ptr = makenextvar ()
            in
              code @alias_code @cast_code
              (* store the value in the struct *)
              @[  LLVM.GetElementPtr (var_val_ptr,LLVM.ptr form_type,LLVM.Variable var_form_type,[LLVM.Int 0,LLVM.Int i])
                , LLVM.Store (t,LLVM.Variable var,LLVM.Variable var_val_ptr)
              ]@(initialize (i+1) xs)
            end

        val code = [
              LLVM.Call (var_malloc, LLVM.ptr LLVM.i8, "malloc", [(LLVM.Int (LLVM.sizeOfType user_type),LLVM.i32)])
            , LLVM.Bitcast (var_T_type, LLVM.ptr LLVM.i8, LLVM.Variable var_malloc, LLVM.ptr LLVM.usertype_parent)
            (* set the form tracker *)
            , LLVM.GetElementPtr (var_form_ptr,LLVM.ptr LLVM.usertype_parent,LLVM.Variable var_T_type,[LLVM.Int 0,LLVM.Int 0])
            , LLVM.Store (LLVM.i32,LLVM.Int (LLVM.getFormIndex form),LLVM.Variable var_form_ptr)
            (* grab a pointer to the data portion *)
            , LLVM.GetElementPtr (var_form_type,LLVM.ptr LLVM.usertype_parent,LLVM.Variable var_T_type,[LLVM.Int 0,LLVM.Int 1])
            , LLVM.Bitcast (var_form_type, LLVM.ptr LLVM.i8, LLVM.Variable var_form_type, LLVM.ptr form_type)
          ]@(initialize 0 (ListPair.zip (types,exps)))@[
              LLVM.Alias (LLVM.Variable var_result, LLVM.Variable var_malloc) 
          ]
      in
        (var_result,user_type,code)
      end
    else
      let
        val argsAndCodes = map (evalArg scope fscope) exps
        val code = (foldr (op @) [] (map (#1) argsAndCodes))
        val args = (map (fn (_,r,t) => (r,t)) argsAndCodes)
        (*change arrays so that they are passed as pointers*)
        val args = map (fn (x,ty) => case ty of
            LLVM.array _ => (x,ty)
            | _ => (x,ty)) args
        val l = makenextvar ()
        val ty = typeForFunc v fscope
      in
        (l,ty,code@[LLVM.Call (l,ty,v,args)])
      end
  | translate (Ast.Apply _) scope fscope =  raise (TranslationError "Can only apply on variables")
    (*| Case of ast*(string*string list*ast) list*)
  | translate (Ast.Case (exp,branches,default_exp)) scope fscope = let
      val (exp_code,exp_res,exp_ty) = evalArg scope fscope exp

      (* make sure we are dealing with a user type *)
      val ty_name = case exp_ty of LLVM.usertype name => name | _ => raise (TranslationError "Case statements are only valid on user defined types")
      (* general idea:
       extract the form id (DONE)
       make a function that creates a block for each, and have it return the code along with id and label pairs
       then turn the id label pairs into jump code
       *)
      val var_T_type = makenextvar ()
      val var_form_ptr = makenextvar ()
      val var_form = makenextvar ()
      val var_result = makenextvar () (*result of each case branch*)
      val label_exit = makenextlabel ()
      val label_default = makenextlabel ()

      (*set up default exp*)
      val (def_code,def_res,def_ty) = evalArg scope fscope default_exp
      val (_,def_code) = setResult var_result (def_res,def_code)

      (* turns an element of the branch list into a (form_id,label,code,ty) tuple *)
      fun handleBranch (form,xids,then_exp) = let
          val form_types = LLVM.getFormTypes form
          val form_id = LLVM.getFormIndex form
          val _ = if length form_types = length xids then () else raise (TranslationError (concat ["Wrong number of variables for form '",form,"'!"]))
          
          val (then_code,then_res,then_ty) = evalArg ((ListPair.zip (xids,form_types))@scope) fscope then_exp
          val (_,then_code) = setResult var_result (then_res,then_code) (*switch the result for the globally chosen one*)

          val label_branch = makenextlabel ()
          val var_struct_ptr = makenextvar ()

          fun extractVars i [] = []
            | extractVars i ((x,ty)::xs) = let
                val var_x = makenextvar ()
              in
                [   LLVM.GetElementPtr (var_x,LLVM.ptr (LLVM.usertype_form (ty_name,form)),LLVM.Variable var_struct_ptr,[LLVM.Int 0,LLVM.Int i])
                  , LLVM.Load (x,LLVM.ptr ty,LLVM.Variable var_x)
                ]@(extractVars (i+1) xs)
              end
          val extract_code = extractVars 0 (ListPair.zip (xids,form_types))

          val code =
            [   (* define the branch label and extract the values *)
                LLVM.DefnLabel label_branch
              , LLVM.GetElementPtr (var_struct_ptr,LLVM.ptr LLVM.usertype_parent,LLVM.Variable var_T_type,[LLVM.Int 0,LLVM.Int 1])
              , LLVM.Bitcast (var_struct_ptr, LLVM.ptr LLVM.i8, LLVM.Variable var_struct_ptr, LLVM.ptr (LLVM.usertype_form (ty_name,form)))
            ]@extract_code@then_code@[
                LLVM.Br (LLVM.Label label_exit)
            ]
        in
        (form_id,label_branch,code,then_ty)
        end

      val branch_info = map handleBranch branches
      (*find the type that every result must be cast to inorder to remain consistent*)
      val highest_type = highestType def_ty (map (fn b => (var_result,#4 b)) branch_info)
      (*add casting code to end of each branches code segment*)
      fun addCastCode (id,label,code,ty) = let
          val (cast_code,ty) = resolveType' [] highest_type [(var_result,ty)]
        in (id,label,code@cast_code,highest_type) end
      val branch_info = map addCastCode branch_info

      (* concat each of the branch segments *)
      val branch_code = List.concat (map #3 branch_info)

      (* finish setting up the default expression*)
      val (def_alias,[var_def]) = ensureVars [def_res]
      val (def_cast,ty) = resolveType' [] highest_type [(var_def,def_ty)]

      (*construct the jump code*)
      fun makeJumps label_next [] = []
        | makeJumps label_next ((id,label)::ids) = let
          val var_cmp = makenextvar ()
          val label_next_next = makenextlabel ()
        in
          [ LLVM.DefnLabel label_next_next
          , LLVM.CmpEq (var_cmp,LLVM.i32,LLVM.Int id,LLVM.Variable var_form)
          , LLVM.CndBr (LLVM.Variable var_cmp,(LLVM.Label label),(LLVM.Label label_next))
          ]::(makeJumps label_next_next ids)
        end

      val id_label_pairs = (map (fn (id,label,_,_) => (id,label)) branch_info)
      (* we create the jump blocks in reverse order so we can avoid having to defnlabels next to eachother 
         so we pass in the exit label, and each block labels itself
         this means that what ends up being the first block will have a useless label so we tail it to drop it *)
      val jump_code = (tl o List.concat o rev) (makeJumps label_default id_label_pairs)

      val code =
        exp_code@[
            LLVM.Bitcast (var_T_type, exp_ty, exp_res, LLVM.ptr LLVM.usertype_parent)
          (* get the form tracker *)
          , LLVM.GetElementPtr (var_form_ptr,LLVM.ptr LLVM.usertype_parent,LLVM.Variable var_T_type,[LLVM.Int 0,LLVM.Int 0])
          , LLVM.Load (var_form,LLVM.ptr LLVM.i32,LLVM.Variable var_form_ptr)
        ]@jump_code@[
            LLVM.DefnLabel label_default
        ]@def_code@def_alias@def_cast@[
            LLVM.Br (LLVM.Label label_exit)
        ]@branch_code@[
            LLVM.DefnLabel label_exit
        ]
    in
      (var_result,highest_type,code)
    end
  | translate (Ast.For (init_exp,cond_exp,step_exp,doexp)) scope fscope = let
      val cnd_label = makenextlabel ()
      val loop_end_label = makenextlabel ()
      val (init_code,init_res,_) = evalArg scope fscope init_exp
      val (cond_code,cond_res,cond_ty) = evalArg scope fscope cond_exp
      val (step_code,step_res,_) = evalArg scope fscope step_exp
      val _ = ensureType LLVM.i1 [cond_ty]
      val (do_code,do_res,_) = evalArg scope fscope doexp
      val res = makenextvar()


      fun containsALoop (Ast.For _) = true
        | containsALoop (Ast.Let (_,e1,e2)) = containsALoop e1 orelse containsALoop e2
        | containsALoop _ = false

      (*unrolls a loop i times*)
      fun doUnrollLoop 0 = []
        | doUnrollLoop i = let
            val loop_next_label = makenextlabel ()
          in
            cond_code@[
              LLVM.CndBr(cond_res,LLVM.Label(loop_next_label),LLVM.Label(loop_end_label))
            , LLVM.DefnLabel(loop_next_label)
            ]@do_code@step_code@(doUnrollLoop (i-1))
          end

      val unrolledLoopCode = case (containsALoop doexp,!config_unroll) of
          (true,_) => doUnrollLoop 1 (*only unroll inner loops*)
        | (_,NONE) => doUnrollLoop 1
        | (_,SOME unroll) => if unroll <= 0 then doUnrollLoop 1 else doUnrollLoop unroll

    in
      (res, LLVM.i32, init_code@[
          LLVM.Br (LLVM.Label cnd_label)
        , LLVM.DefnLabel cnd_label
        ]@unrolledLoopCode@[
          LLVM.Br(LLVM.Label(cnd_label))
        , LLVM.DefnLabel(loop_end_label)
        ]@[
          LLVM.Alias (LLVM.Variable res,LLVM.Int 0) (*For loops have no "value"*)
        ])
    end
  | translate (Ast.If (bexp,texp,fexp)) scope fscope = let
      val [l_true,l_false,l_out] = map makenextlabel [(),(),()]
      val result = makenextvar ()
      (*conditional code and result*)
      val (bcode,bres,bty) = evalArg scope fscope bexp
      val _ = ensureType LLVM.i1 [bty]
      (*set the result of both the true and false expressions to result*)
      val (tres,tty,tcode) = translate texp scope fscope
      val (fres,fty,fcode) = translate fexp scope fscope
      val (_,tcode) = setResult result (LLVM.Variable tres,tcode)
      val (_,fcode) = setResult result (LLVM.Variable fres,fcode)
      val exp_ty = highestType fty [(tres,tty)] (*what type should the be cast too, or error or whatever*)
      (*need separate casting code*)
      val (t_cast_code,_) = resolveType' [] exp_ty [(result,tty)]
      val (f_cast_code,_) = resolveType' [] exp_ty [(result,fty)]
    in
      (result, exp_ty, bcode@[
          LLVM.CndBr (bres,(LLVM.Label l_true),(LLVM.Label l_false))
        , LLVM.DefnLabel l_true
      ]@tcode@t_cast_code@[
          LLVM.Br (LLVM.Label l_out)
        , LLVM.DefnLabel l_false
      ]@fcode@f_cast_code@[
          LLVM.Br (LLVM.Label l_out)
        , LLVM.DefnLabel l_out
      ])
    end
  | translate (Ast.AssignArray (exp,index,val_exp)) scope fscope = let
        val (exp_code,exp_res,exp_ty) = evalArg scope fscope exp
        val (i_code,i_res,i_ty) = evalArg scope fscope index
        val (val_code,val_res,val_ty) = evalArg scope fscope val_exp

        (*val _ = case val_exp of Ast.EmptyArray _ => print "FUcK YEAH!\n" | _ => print "FUCK NO!\n"*)

        (* error checking *)
        val base_ty = case exp_ty of LLVM.array t => t | _ => raise (TranslationError "Can only index arrays!!!")
        val _ = case i_ty of LLVM.i32 => () | _ => raise (TranslationError "Index of an array must be an int!")
        (*casting and error checking*)
        val (val_alias_code,[var]) = ensureVars [val_res]
        (* val (val_cast_code,_) = resolveType' [] base_ty [(var,val_ty)] *)
        val val_cast_code = []

        val (alias_code,[var_exp]) = ensureVars [exp_res]
        val (ptr_res,ptr_ty,ptr_code) = calculateElemPtr var_exp exp_ty i_res
        val var_res = makenextvar ()

        val code = exp_code@i_code@alias_code@ptr_code@val_code@val_alias_code@val_cast_code@[
            LLVM.Store (base_ty,val_res,LLVM.Variable ptr_res)
          , LLVM.Alias (LLVM.Variable var_res,val_res)
        ]
      in
        (var_res,base_ty,code)
      end
  | translate (Ast.Assign (id,exp)) scope fscope = 
    let
      val (vres,vcode) = setVariable id exp scope fscope
      val ty = getTypeForVar scope id
    in
      (vres,ty,vcode)
    end
  | translate (Ast.Let (id,exp,inexp)) scope fscope =  let
      (*val (vcode,varg) = evalArg exp*)
      (*too tired to think of how to do this in an intelligent way, just grab the type of the expression...*)
      val (_,vty,_) = translate exp scope fscope
      (*
      val new_scope = (id,(case exp of
              (Ast.Array exps) => vty
            | (Ast.EmptyArray (ty,dim)) => LLVM.array ty
            | _ => vty
          ))::scope
      *)
      val new_scope = (id,vty)::scope

      val (vres,vcode) = setVariable id exp new_scope fscope
      val (res,ty,code) = translate inexp new_scope fscope
    in
      (res,ty,vcode@code)
    end

  fun compileFun scope fscope ((fid,xids,ty,fexp)) = let
      val (fcode,farg,fty) = evalArg (xids@scope) fscope fexp
      (* change xids so that it doesn't affect the scope*)
      (* arrays are weird, sometimes the look like pointers, sometimes not..*)
      val xids = map (fn (x,ty) => case ty of
          LLVM.array _ => (x,ty)
          | _ => (x,ty)) xids
      val (alias_code,[var]) = ensureVars [farg]
      val (cast_code,ty) = resolveType' [] ty [(var,fty)]
      val methodBody = 
        (*execute the method body*)
        fcode@
        alias_code@
        cast_code@
        (*add the return statement*)
        [LLVM.Ret (ty, farg)]
        (* lists are silly, just pass the args in backwards *)
      val _ = addMethod (fid,ty,rev xids,methodBody)
    in
      (*translate inexp scope fscope*)
      ()
    end

  (*make a scope of all functions and their types*)
  fun getFunScope [] = []
    | getFunScope ((id,_,ty,_)::funs) = (id,ty)::(getFunScope funs)

  fun compile (Ast.CompilerTarget (types,funs,ast)) = let
    val _ = map LLVM.addUserType types (*add the user types to the scope*)
    val funScope = ("rand",LLVM.i32)::(getFunScope funs)

    val _ = map (compileFun [] funScope) funs
    val (mainBody,vres,vty) = evalArg [] funScope ast

    val res = case vres of
        (LLVM.Variable v) => v
      | (LLVM.Int i) => Int.toString(i)
      | (LLVM.Float i) => Real.toString(i)
      | (LLVM.Bool b) => Int.toString(b)
      | (LLVM.Label v) => concat ["label %",v]
    val l = makenextvar ()
    val _ = addMethod (
          "main"
        , LLVM.i32
        , []
        , mainBody@[
              (*LLVM.Raw (concat["%",l," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 ",res,")"])*)
              (*LLVM.Print (l,vres)
            , *)LLVM.Ret (vty,vres)
          ]
      )
    in
      ()
    end


end
