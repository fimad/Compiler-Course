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
            | any => any)]
        | setResult_help (x::xs) = x::(setResult_help xs)
    in
      (newRes, setResult_help code)
    end

  fun evalArg scope (Ast.Int i) = ([],(LLVM.Int i),LLVM.i32)
    | evalArg scope (Ast.Float f) = ([],(LLVM.Float f),LLVM.float)
    | evalArg scope (Ast.Bool b) = ([],(LLVM.Bool b),LLVM.i1)
    | evalArg scope expr = let
        val (res,ty,code) = translate expr scope
      in
        (code, (LLVM.Variable res), ty)
      end

  (*takes a list of variables and types, and returns code for casting (can resuse names, they will get renamed later), and final type*)
  and resolveType' acc [] = acc
    | resolveType' acc (x::xs) =  acc

  and resolveType [] = raise (TranslationError "Expected Type but none found...")
    | resolveType (x::xs) = resolveType' x xs

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

  and calculateArrayIndex ptr ty [] [] scope = (ptr,[],ty)
    | calculateArrayIndex ptr ty [] _ scope = raise (TranslationError (concat ["not enuff indices... yo.. in '",ptr,"'"]))
    | calculateArrayIndex ptr ty _ [] scope = raise (TranslationError (concat ["Indices into array '",ptr,"' have more dimensions than definition."]))
    | calculateArrayIndex ptr ty (i::indices) (d::dims) scope = let
        val (i_code,i_res) = evalArg scope i 
        val next_ptr = makenextvar ()
        val (res_ptr,next_code,res_ty) = (case ty of
              LLVM.array (_,sub_ty) => calculateArrayIndex next_ptr sub_ty indices dims scope
            | _ => (next_ptr,[],ty)
          )
        val code = i_code@[LLVM.GetElementPtr (next_ptr,LLVM.ptr ty,LLVM.Variable ptr,i_res)]@next_code
      in
        (res_ptr,code,res_ty)
      end
    | calculateArrayIndex ptr _ _ _ scope = raise (TranslationError "Attempt to index on a not an array!")

  and arrayDimFromExps exps scope = let
      (*Makes sure all the elements of list are equal*)
      fun all_equal [] = true
        | all_equal [a] = true
        | all_equal (a::b::cs) = if a <> b then false else all_equal (b::cs)
      (*turns an expression into a dimension*)
      fun elemToDim exp =
          (case exp of 
              Ast.Array sub_exps => arrayDimFromExps sub_exps scope
            | Ast.EmptyArray dim => dim
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
  and setVariable result exp scope = 
    (case exp of
      (*needed for assign and let*)
      (* (Ast.Var x) => (result, [LLVM.Add (result,LLVM.i32, (LLVM.Num 0), (LLVM.Variable x))]) *)
        (Ast.Var x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Variable x))])
      | (Ast.Int x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Int x))])
      | (Ast.Float x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Float x))])
      | (Ast.Bool x) => (result, [LLVM.Alias ((LLVM.Variable result),(LLVM.Bool x))])
      (*needed for everything eles*)
      | exp => setResult result (translate exp scope))

  and translate (Ast.Print ast) scope = let
      val pres = makenextvar ()
      val (code,res,ty) = evalArg scope ast
    in
      (pres,LLVM.i32,code@[LLVM.Print (pres,res)])
    end
  | translate (Ast.Dim (level,id)) scope = let
      val i = makenextvar ()
      fun levelDimOfType 0 (LLVM.array (dim,ty)) = dim
        | levelDimOfType level (LLVM.array (dim,ty)) = levelDimOfType (level-1) ty
        | levelDimOfType _ _ = 0
    in
        (i,LLVM.i32,[LLVM.Alias (LLVM.Variable i, LLVM.Int (levelDimOfType level (getTypeForVar scope id)))])
    end
  | translate (Ast.Block asts) scope = let
      val i = makenextvar ()
    in
      foldl (fn (exp,(_,_,prev_code)) => let
              val (res,ty,code) = translate exp scope
            in
              (res,ty,prev_code@code)
            end
            ) (i,LLVM.i32,[LLVM.Alias (LLVM.Variable i,LLVM.Int 0)]) asts
    end
  | translate (Ast.Int (i)) scope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Int i))]
    in (l,LLVM.i32,code) end
  | translate (Ast.Float (i)) scope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Float i))]
    in (l,LLVM.float,code) end
  | translate (Ast.Bool (i)) scope = let
      val l = makenextvar ()
      val code = [LLVM.Alias ((LLVM.Variable l), (LLVM.Bool i))]
    in (l,LLVM.i1,code) end
  | translate (Ast.Array (exps)) scope =  let
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

      val dim = arrayDimFromExps exps scope
      val new_res = makenextvar ()
      (*TODO FIND TYPE FOR INITIALIZED ARRAYS*)
      val (res,ty,create_code) = translate (Ast.EmptyArray (dim)) scope
      (*val _ = map (fn d => (map (print o Int.toString) d,print "\n")) (enumDims dim)*)

      val update_code = foldl (fn (i,prev_code) => let
              val (ptr,ptr_code,ty) = calculateArrayIndex res (llvmTypeForDim LLVM.i32 dim) (map Ast.Int i) dim scope
              val (exp_code,exp_res,exp_ty) = evalArg scope (getExpForIndex i exps)
            in
              prev_code@ptr_code@exp_code@[LLVM.Store (ty,exp_res,LLVM.Variable ptr)]
            end
          ) [] (enumDims dim)
    in
      (new_res,ty,create_code@update_code@[LLVM.Alias (LLVM.Variable new_res,LLVM.Variable res)])
    end
  | translate (Ast.EmptyArray (pty,dims)) scope =  let
      val l = makenextvar ()
      val ty = llvmTypeForDim pty dims
      val code = [LLVM.Alloca (l,ty,1)]
    in
      (l,ty,code)
    end
  | translate (Ast.ArrayIndex (id,indices)) scope = 
      (case getTypeForVar scope id of
        (ty as LLVM.array _) => let
            (*val ty = llvmTypeForDim LLVM.i32 dim*)
            val dim = dimFromLLVMType ty
            val base_ty = arrayBaseType ty
            val (i_ptr,i_code,i_ty) = calculateArrayIndex id ty indices dim scope
            val res = makenextvar ()
            val code = i_code@[LLVM.Load (res,LLVM.ptr i_ty,LLVM.Variable i_ptr)]
          in
            (res,base_ty,code)
          end
        | _ => raise (TranslationError (concat ["Attempt to index non-array variable '",id,"'"]))
      )
  | translate (Ast.Var (x)) scope =  let
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
  | translate (Ast.NotEq (a,b)) scope = let
      val (code1,arg1,ty1) = evalArg scope a 
      val (code2,arg2,ty2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpNe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.And (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.And (l,LLVM.i1,arg1,arg2)])
    end
  | translate (Ast.Or (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Or (l,LLVM.i1,arg1,arg2)])
    end
  | translate (Ast.Eq (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpEq (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Less (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpLt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.LessEq (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpLe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.More (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpGt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.MoreEq (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpGe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Not (a)) scope = let
      val (code1,arg1) = evalArg scope a 
      val l = makenextvar ()
    in
      (l,code1@[LLVM.Xor (l,LLVM.i1,(LLVM.Int 1),arg1)])
    end
  | translate (Ast.Plus (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Add (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Minus (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Sub (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Mult (a,b)) scope = let
      val (code1,arg1) = evalArg scope a 
      val (code2,arg2) = evalArg scope b 
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Mul (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Div (a,b)) scope = let
      val (code1,arg1) = evalArg scope a
      val (code2,arg2) = evalArg scope b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Div (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Apply ((Ast.Var v),exps)) scope =  let
      val argsAndCodes = map (evalArg scope) exps
      val code = (foldr (op @) [] (map (#1) argsAndCodes))
      val args = (map (#2) argsAndCodes)
      val l = makenextvar ()
    in
      (l,code@[LLVM.Call (l,LLVM.i32,v,args)])
    end
  | translate (Ast.Apply _) scope =  raise (TranslationError "Can only apply on variables")
  | translate (Ast.For (init_exp,cond_exp,step_exp,doexp)) scope = let
      val cnd_label = makenextlabel ()
      val loop_start_label = makenextlabel ()
      val loop_end_label = makenextlabel ()
      val (init_code,init_res) = evalArg scope init_exp
      val (cond_code,cond_res) = evalArg scope cond_exp
      val (step_code,step_res) = evalArg scope step_exp
      val (do_code,do_res) = evalArg scope doexp
      val res = makenextvar()
    in
      (res, init_code@[
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
  | translate (Ast.If (bexp,texp,fexp)) scope = let
      val [l_true,l_false,l_out] = map makenextlabel [(),(),()]
      val result = makenextvar ()
      (*conditional code and result*)
      val (bcode,bres) = evalArg scope bexp
      (*set the result of both the true and false expressions to result*)
      val (_,tcode) = setResult result (translate texp scope)
      val (_,fcode) = setResult result (translate fexp scope)
    in
      (result, bcode@[
          LLVM.CndBr (bres,(LLVM.Label l_true),(LLVM.Label l_false))
        , LLVM.DefnLabel l_true
      ]@tcode@[
          LLVM.Br (LLVM.Label l_out)
        , LLVM.DefnLabel l_false
      ]@fcode@[
          LLVM.Br (LLVM.Label l_out)
        , LLVM.DefnLabel l_out
      ])
    end
  | translate (Ast.AssignArray (id,index,exp)) scope = 
    (case getTypeForVar scope id of
        (ty as LLVM.array _) => let
            (*val ty = llvmTypeForDim LLVM.i32 dim*)
            val dim = dimFromLLVMType ty
            val (i_ptr,i_code,i_ty) = calculateArrayIndex id ty index dim scope
            val (vcode,vres) = evalArg scope exp
            val code = i_code@vcode@[LLVM.Store (i_ty,vres,LLVM.Variable i_ptr)]
          in
            (i_ptr,code)
          end
      | _ => raise (TranslationError (concat ["Attempt to index non-array variable '",id,"'"]))
    )
  | translate (Ast.Assign (id,exp)) scope = 
  (*let
      val (vcode,varg) = evalArg exp
      val l = makenextvar ()
    in
      (l, vcode@[
          LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
        , LLVM.Load (l,LLVM.pi32,(LLVM.Variable id))
      ])
    end *)
    setVariable id exp scope
  | translate (Ast.Let (id,exp,inexp)) scope =  let
      (*val (vcode,varg) = evalArg exp*)
      val new_scope = (id,(case exp of
              (Ast.Array exps) => llvmTypeForDim LLVM.i32 (arrayDimFromExps exps scope)
            | (Ast.EmptyArray dim) => llvmTypeForDim LLVM.i32 dim
            | _ => LLVM.i32
          ))::scope
      val (vres,vcode) = setVariable id exp new_scope
      val (res,code) = translate inexp new_scope
    in
    (*
      (res, vcode@[
          LLVM.Alloca (id,LLVM.i32)
        , LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
      ]@code)
      *)
      (res, vcode@code)
    end
  | translate (Ast.Fun (fid,xids,fexp,inexp)) scope = let
      fun zipI32 [] = []
        | zipI32 (x::xs) = (x,LLVM.i32)::(zipI32 xs)
      fun zipInt [] = []
        | zipInt (x::xs) = (x,LLVM.i32)::(zipInt xs)
      val (fcode,farg) = evalArg (xids@scope) fexp
      val methodBody = 
        (*execute the method body*)
        fcode@
        (*add the return statement*)
        [LLVM.Ret (LLVM.i32, farg)]
        (*TODO INFER THE RETURN TYPE OF THE METHOD*)
      val _ = addMethod (fid,LLVM.i32,xids,methodBody)
    in
      translate inexp scope
    end

  fun compile ast = let
    val (mainBody,vres) = evalArg [] ast
    val res = case vres of
        (LLVM.Variable v) => v
      | (LLVM.Int i) => Int.toString(i)
      | (LLVM.Float i) => Real.toString(i)
      | (LLVM.Bool b) => Bool.toString(b)
      | (LLVM.Label v) => concat ["label %",v]
    val l = makenextvar ()
    val _ = addMethod (
          "main"
        , LLVM.i32
        , []
        , mainBody@[
              (*LLVM.Raw (concat["%",l," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 ",res,")"])*)
              (*LLVM.Print (l,vres)
            , *)LLVM.Ret (LLVM.i32,vres)
          ]
      )
    in
      ()
    end


end
