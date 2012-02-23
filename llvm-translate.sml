(* Will Coster *)

structure LLVM_Translate = 
struct

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

  fun evalArg (Ast.Num i) = ([],(LLVM.Num i))
    | evalArg expr = let
        val (res,code) = translate expr
      in
        (code, (LLVM.Variable res))
      end

  and translate (Ast.Num (i)) = let
      val l = makenextvar ()
      val code = [LLVM.Add (l,LLVM.i32, (LLVM.Num 0), (LLVM.Num i))]
    in
      (l,code)
    end
  | translate (Ast.Var (x)) =  let
      val l = makenextvar ()
      val code = [LLVM.Load (l,LLVM.pi32,(LLVM.Variable x))]
    in
      (l,code)
    end
  | translate (Ast.Eq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpEq (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Less (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpLt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.LessEq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpLe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.More (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpGt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.MoreEq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.CmpGe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Not (a)) = let
      val (code1,arg1) = evalArg a
      val l = makenextvar ()
    in
      (l,code1@[LLVM.Xor (l,LLVM.i1,(LLVM.Num 1),arg1)])
    end
  | translate (Ast.Plus (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Add (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Minus (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Sub (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Mult (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Mul (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Div (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextvar ()
    in
      (l,code1@code2@[LLVM.Div (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Ast.Apply ((Ast.Var v),exps)) =  let
      val argsAndCodes = map evalArg exps
      val code = (foldr (op @) [] (map (#1) argsAndCodes))
      val args = (map (#2) argsAndCodes)
      val l = makenextvar ()
    in
      (l,code@[LLVM.Call (l,LLVM.i32,v,args)])
    end
  | translate (Ast.Apply _) =  raise (TranslationError "Can only apply on variables")
  | translate (Ast.For (id,toexp,byexp,doexp,inexp)) = let
      val cnd_label = makenextlabel ()
      val update_label = makenextlabel ()
      val loop_start_label = makenextlabel ()
      val loop_end_label = makenextlabel ()
      val (by_code,by_res) = evalArg byexp
      val (to_code,to_res) = evalArg toexp
      val (do_code,do_res) = evalArg doexp
      val (in_res,in_code) = translate inexp
      val id_var = makenextvar ()
      val id_cmp_var = makenextvar ()
      val add_var = makenextvar ()
      val cmp_var = makenextvar ()
    in
      (in_res, to_code@by_code@[
          LLVM.Br(LLVM.Label(cnd_label))
        , LLVM.DefnLabel(update_label)
        , LLVM.Load(id_var,LLVM.pi32,LLVM.Variable(id))
        , LLVM.Add(add_var,LLVM.i32,LLVM.Variable(id_var),by_res)
        , LLVM.Store(LLVM.i32,LLVM.Variable(add_var),LLVM.Variable(id))
        , LLVM.Br(LLVM.Label(cnd_label))
        , LLVM.DefnLabel(cnd_label)
        , LLVM.Load(id_cmp_var,LLVM.pi32,LLVM.Variable(id))
        , LLVM.CmpNe(cmp_var,LLVM.i32,LLVM.Variable(id_cmp_var),to_res)
        , LLVM.CndBr(LLVM.Variable(cmp_var),LLVM.Label(loop_start_label),LLVM.Label(loop_end_label))
        , LLVM.DefnLabel(loop_start_label)
       ]@do_code@[
          LLVM.Br(LLVM.Label(update_label))
        , LLVM.DefnLabel(loop_end_label)
       ]@in_code)
    end
  | translate (Ast.If (bexp,texp,fexp)) = let
      val [l1,l2,l3] = map makenextlabel [(),(),()]
      val [l4,l5] = map makenextvar [(),()]
      val (bcode,bres) = evalArg bexp
      val (tcode,tres) = evalArg texp
      val (fcode,fres) = evalArg fexp
    in
      (l5, [
          LLVM.Alloca (l4,LLVM.i32)
      ]@bcode@[
          LLVM.CndBr (bres,(LLVM.Label l1),(LLVM.Label l2))
        , LLVM.DefnLabel l1
      ]@tcode@[
          LLVM.Store (LLVM.i32,tres,(LLVM.Variable l4))
        , LLVM.Br (LLVM.Label l3)
        , LLVM.DefnLabel l2
      ]@fcode@[
          LLVM.Store (LLVM.i32,fres,(LLVM.Variable l4))
        , LLVM.Br (LLVM.Label l3)
        , LLVM.DefnLabel l3
        , LLVM.Load (l5,LLVM.pi32,(LLVM.Variable l4))
      ])
    end
  | translate (Ast.Assign (id,exp)) = let
      val (vcode,varg) = evalArg exp
      val l = makenextvar ()
    in
      (l, vcode@[
          LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
        , LLVM.Load (l,LLVM.pi32,(LLVM.Variable id))
      ])
    end
  | translate (Ast.Let (id,exp,inexp)) = let
      val (vcode,varg) = evalArg exp
      val (res,code) = translate inexp
    in
      (res, vcode@[
          LLVM.Alloca (id,LLVM.i32)
        , LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))
      ]@code)
    end
  | translate (Ast.LetSta (fid,xids,fexp,inexp)) = let
      fun zipI32 [] = []
        | zipI32 (x::xs) = (x,LLVM.i32)::(zipI32 xs)
      val (fcode,farg) = evalArg fexp
      val methodBody = 
        (*allocate memory for the parameters*)
        (map (fn x => LLVM.Alloca (x,LLVM.i32)) xids)@
        (*store the parameters in the allocated memory*)
        (map (fn x =>
          LLVM.Store (LLVM.i32,LLVM.Variable(concat ["_",x]),LLVM.Variable(x))
        ) xids)@
        (*execute the method body*)
        fcode@
        (*add the return statement*)
        [LLVM.Ret (LLVM.i32, farg)]
      val _ = addMethod (fid,LLVM.i32,(zipI32 (map (fn x => concat ["_",x]) xids)),methodBody)
    in
      translate inexp
    end
    (*treat dyn and static the same for now *)
  | translate (Ast.LetDyn (fid,xids,fexp,inexp)) =  translate (Ast.LetSta (fid,xids,fexp,inexp))

  fun compile ast = let
    val (mainBody,vres) = evalArg ast
    val res = case vres of
        (LLVM.Variable v) => concat ["%",v]
      | (LLVM.Num i) => Int.toString(i)
      | (LLVM.Label v) => concat ["label %",v]
    val l = makenextvar ()
    val _ = addMethod (
          "main"
        , LLVM.i32
        , []
        , mainBody@[
              LLVM.Raw (concat["%",l," = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 ",res,")"])
            , LLVM.Ret (LLVM.i32,vres)
          ]
      )
    in
      ()
    end


end
