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
            | any => any)]
        | setResult_help (x::xs) = x::(setResult_help xs)
    in
      (newRes, setResult_help code)
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
    | llvmTypeForDim ty (d::im) = LLVM.array (d,llvmTypeForDim ty im)

  and dimFromLLVMType (LLVM.array (i,sub)) = i::(dimFromLLVMType sub)
    | dimFromLLVMType _ = []

  and arrayBaseType (LLVM.array (i,sub)) = arrayBaseType sub
    | arrayBaseType ty = ty

  and calculateArrayIndex ptr ty [] [] _ _ = (ptr,[],ty)
    | calculateArrayIndex ptr ty [] _ _ _ = (ptr,[],ty)
    (*| calculateArrayIndex ptr ty [] _ _ _ = raise (TranslationError (concat ["not enuff indices... yo.. in '",ptr,"'"]))*)
    | calculateArrayIndex ptr ty _ [] _ _ = raise (TranslationError (concat ["Indices into array '",ptr,"' have more dimensions than definition."]))
    | calculateArrayIndex ptr ty (i::indices) (d::dims) scope fscope = let
        val (i_code,i_res,i_ty) = evalArg scope fscope i 
        val next_ptr = makenextvar ()
        val (res_ptr,next_code,res_ty) = (case ty of
              LLVM.array (_,sub_ty) => calculateArrayIndex next_ptr sub_ty indices dims scope fscope
            | _ => (next_ptr,[],ty)
          )
        val code = i_code@[LLVM.GetElementPtr (next_ptr,LLVM.ptr ty,LLVM.Variable ptr,i_res)]@next_code
      in
        (res_ptr,code,res_ty)
      end
    | calculateArrayIndex ptr _ _ _ _ _ = raise (TranslationError "Attempt to index on a not an array!")

  and arrayDimFromExps exps scope fscope = let
      (*Makes sure all the elements of list are equal*)
      fun all_equal [] = true
        | all_equal [a] = true
        | all_equal (a::b::cs) = if a <> b then false else all_equal (b::cs)
      (*turns an expression into a dimension*)
      fun elemToDim exp =
          (case exp of 
              Ast.Array sub_exps => arrayDimFromExps sub_exps scope fscope
            | Ast.EmptyArray (_,dim) => dim
            | exp => [])
      val first = length exps
      val rest_list = map elemToDim exps
    in
      if all_equal rest_list then
        (first::(hd rest_list))
      else
        raise (TranslationError "Sub array dimensions do not match")
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
          val (a,_,b) = translate exp scope fscope
        in
          setResult result (a,b)
        end)

  and typeForFunc id [] = raise (TranslationError (concat ["Function '",id,"' not defined"]))
    | typeForFunc id ((id',ty)::ids) = if id = id' then ty else typeForFunc id ids

  and translate (Ast.Print ast) scope fscope = let
      val pres = makenextvar ()
      val (code,res,ty) = evalArg scope fscope ast
    in
      (pres,LLVM.i32,code@[LLVM.Print (pres,ty,res)])
    end
  | translate (Ast.Dim (level,id)) scope fscope = let
      val i = makenextvar ()
      fun levelDimOfType 0 (LLVM.array (dim,ty)) = dim
        | levelDimOfType level (LLVM.array (dim,ty)) = levelDimOfType (level-1) ty
        | levelDimOfType _ _ = 0
    in
        (i,LLVM.i32,[LLVM.Alias (LLVM.Variable i, LLVM.Int (levelDimOfType level (getTypeForVar scope id)))])
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
      (* hopefully will return the expression that corresponds to a given index into the array *)
      fun getExpForIndex [] [] = raise (TranslationError "Something terrible has happened!")
        | getExpForIndex [] (exp::exps) = raise (TranslationError "Something terrible but not that first thing has happened!")
        | getExpForIndex _ [] =  raise (TranslationError "Something terrible but not that first or second thing has happened!")
        | getExpForIndex [0] (exp::exps) = exp
        | getExpForIndex (0::indices) ((Ast.Array sub_exps)::exps) = getExpForIndex indices sub_exps
        | getExpForIndex (0::indices) (_::exps) = raise (TranslationError "Array dimensions do not match for all elements yo!")
        | getExpForIndex (i::indices) (exp::exps) = getExpForIndex ((i-1)::indices) exps

      fun enumDims [] = [[]]
        | enumDims (1::dims) = (map (fn a => 0::a) (enumDims dims))
        | enumDims (d::dims) = (map (fn a => (d-1)::a) (enumDims dims))@(enumDims ((d-1)::dims))

      val dim = arrayDimFromExps exps scope fscope
      val new_res = makenextvar ()
      (* Find the highest type in expressions *)
      val ((_,ty)::types) = map (fn d => let val (r,t,_) = translate (getExpForIndex d exps) scope fscope in (r,t) end) (enumDims dim)
      val high_type = highestType ty types

      val (res,ty,create_code) = translate (Ast.EmptyArray (high_type,dim)) scope fscope
      (*val _ = map (fn d => (map (print o Int.toString) d,print "\n")) (enumDims dim)*)

      val update_code = foldl (fn (i,prev_code) => let
              val (ptr,ptr_code,ty) = calculateArrayIndex res (llvmTypeForDim high_type dim) (map Ast.Int i) dim scope fscope
              val (exp_code,exp_res,exp_ty) = evalArg scope fscope (getExpForIndex i exps)
              val (alias_code,[var]) = ensureVars [exp_res]
              val (exp_cast,exp_ty) = resolveType' [] high_type [(var,exp_ty)]
            in
              prev_code@ptr_code@exp_code@alias_code@exp_cast@[LLVM.Store (high_type,LLVM.Variable var,LLVM.Variable ptr)]
            end
          ) [] (enumDims dim)
    in
      (new_res,ty,create_code@update_code@[LLVM.Alias (LLVM.Variable new_res,LLVM.Variable res)])
    end
  | translate (Ast.EmptyArray (pty,dims)) scope fscope =  let
      val l = makenextvar ()
      val l2 = makenextvar ()
      val ty = llvmTypeForDim pty dims
      (*val code = [LLVM.Alloca (l,ty,1)]*)
      val code = [
          LLVM.Call (l,LLVM.ptr LLVM.i8,"malloc",[(LLVM.Int (LLVM.sizeOfType ty),LLVM.i32)])
        , LLVM.Bitcast (l2,LLVM.ptr LLVM.i8,LLVM.Variable l,LLVM.ptr ty)
      ]
    in
      (l2,ty,code)
    end
  | translate (Ast.ArrayIndex (id,indices)) scope fscope = 
      (case getTypeForVar scope id of
        (ty as LLVM.array _) => let
            (*val ty = llvmTypeForDim LLVM.i32 dim*)
            val dim = dimFromLLVMType ty
            (*val base_ty = arrayBaseType ty*)
            val (i_ptr,i_code,i_ty) = calculateArrayIndex id ty indices dim scope fscope
            val res' = makenextvar ()
            (* if we are indexing a sub array then we don't need to load *)
            val (res,code) = (
                case i_ty of
                  LLVM.array _ => (i_ptr,i_code)
                  | _ => (res',i_code@[LLVM.Load (res',LLVM.ptr i_ty,LLVM.Variable i_ptr)])
              )
          in
            (res,i_ty,code)
          end
        | _ => raise (TranslationError (concat ["Attempt to index non-array variable '",id,"'"]))
      )
  | translate (Ast.Var (x)) scope fscope =  let
  (*
      val l = makenextvar ()
      val code = [LLVM.Load (l,LLVM.pi32,(LLVM.Variable x))]
      val l = makenextvar ()
      *)
      (* val code = [LLVM.Add (l,LLVM.i32, (LLVM.Num 0), (LLVM.Variable x))] *)
      val ty = getTypeForVar scope x (*we don't really care what the type is, we care if it's bound and this will bitch if it isn't*)
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
  | translate (Ast.Apply ((Ast.Var v),exps)) scope fscope =  let
      val argsAndCodes = map (evalArg scope fscope) exps
      val code = (foldr (op @) [] (map (#1) argsAndCodes))
      val args = (map (fn (_,r,t) => (r,t)) argsAndCodes)
      (*change arrays so that they are passed as pointers*)
      val args = map (fn (x,ty) => case ty of
          LLVM.array _ => (x,LLVM.ptr ty)
          | _ => (x,ty)) args
      val l = makenextvar ()
      val ty = typeForFunc v fscope
    in
      (l,ty,code@[LLVM.Call (l,ty,v,args)])
    end
  | translate (Ast.Apply _) scope fscope =  raise (TranslationError "Can only apply on variables")
  | translate (Ast.For (init_exp,cond_exp,step_exp,doexp)) scope fscope = let
      val cnd_label = makenextlabel ()
      val loop_start_label = makenextlabel ()
      val loop_end_label = makenextlabel ()
      val (init_code,init_res,_) = evalArg scope fscope init_exp
      val (cond_code,cond_res,cond_ty) = evalArg scope fscope cond_exp
      val (step_code,step_res,_) = evalArg scope fscope step_exp
      val _ = ensureType LLVM.i1 [cond_ty]
      val (do_code,do_res,_) = evalArg scope fscope doexp
      val res = makenextvar()
    in
      (res, LLVM.i32, init_code@[
          LLVM.Br (LLVM.Label cnd_label)
        , LLVM.DefnLabel cnd_label
        ]@cond_code@[
          LLVM.CndBr(cond_res,LLVM.Label(loop_start_label),LLVM.Label(loop_end_label))
        , LLVM.DefnLabel(loop_start_label)
        ]@do_code@step_code@[
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
      val (_,tcode) = setResult result (tres,tcode)
      val (_,fcode) = setResult result (fres,fcode)
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
  | translate (Ast.AssignArray (id,index,exp)) scope fscope = 
    (case getTypeForVar scope id of
        (ty as LLVM.array _) => let
            (*val ty = llvmTypeForDim LLVM.i32 dim*)
            val dim = dimFromLLVMType ty
            val (i_ptr,i_code,i_ty) = calculateArrayIndex id ty index dim scope fscope
            val (vcode,vres,vty) = evalArg scope fscope exp
            val (alias_code,[var]) = ensureVars [vres]
            val (cast_code,_) = resolveType' [] i_ty [(var,vty)]
            val code = i_code@vcode@alias_code@cast_code@[LLVM.Store (i_ty,LLVM.Variable var,LLVM.Variable i_ptr)]
          in
            (i_ptr,i_ty,code)
          end
      | _ => raise (TranslationError (concat ["Attempt to index non-array variable '",id,"'"]))
    )
  | translate (Ast.Assign (id,exp)) scope fscope = 
  (*let
      val (vcode,varg) = evalArg exp
      val l = makenextvar ()
    in
      (l, vcode@[
          LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
        , LLVM.Load (l,LLVM.pi32,(LLVM.Variable id))
      ])
    end *)
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
      val new_scope = (id,(case exp of
              (Ast.Array exps) => llvmTypeForDim (arrayBaseType vty) (arrayDimFromExps exps scope fscope)
            | (Ast.EmptyArray (ty,dim)) => llvmTypeForDim ty dim
            | _ => vty
          ))::scope

      val (vres,vcode) = setVariable id exp new_scope fscope
      val (res,ty,code) = translate inexp new_scope fscope
    in
    (*
      (res, vcode@[
          LLVM.Alloca (id,LLVM.i32)
        , LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
      ]@code)
      *)
      (res,ty,vcode@code)
    end
  | translate (Ast.Fun (fid,xids,ty,fexp,inexp)) scope fscope = let
      fun zipI32 [] = []
        | zipI32 (x::xs) = (x,LLVM.i32)::(zipI32 xs)
      fun zipInt [] = []
        | zipInt (x::xs) = (x,LLVM.i32)::(zipInt xs)
      val (fcode,farg,fty) = evalArg (xids@scope) fscope fexp
      (* change xids so that it doesn't affect the scope*)
      (* arrays are weird, sometimes the look like pointers, sometimes not..*)
      val xids = map (fn (x,ty) => case ty of
          LLVM.array _ => (x,LLVM.ptr ty)
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
      translate inexp scope fscope
    end

  (*make a scope of all functions and their types*)
  fun getFunScope (Ast.Fun (id,_,ty,_,exp)) = (id,ty)::(getFunScope exp)
    | getFunScope (Ast.Let (_,_,exp)) = getFunScope exp
    | getFunScope _ = []

  fun compile ast = let
    val funScope = getFunScope ast
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
