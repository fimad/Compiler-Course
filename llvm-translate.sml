(* Will Coster *)

structure LLVM_Translate = 
struct

  val curlabel = ref 0
  fun nextlabel () = concat [Int.toString(!curlabel)]
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

  exception TranslationError of string;

  fun evalArg (Ast.Num i) = ([],(LLVM.Num i))
    | evalArg expr = let
        val (res,code) = translate expr
      in
        (code, (LLVM.Variable res))
      end

  and translate (Ast.Num (i)) = let
      val l = makenextlabel ()
      val code = [LLVM.Add (l,LLVM.i32, (LLVM.Num 0), (LLVM.Num i))]
    in
      (l,code)
    end
  | translate (Ast.Var (x)) =  let
      val l = makenextlabel ()
      val code = [LLVM.Load (l,LLVM.pi32,(LLVM.Variable x))]
    in
      (l,code)
    end
  | translate (Eq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.CmpEq (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Less (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.CmpLt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (LessEq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.CmpLe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (More (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.CmpGt (l,LLVM.i32,arg1,arg2)])
    end
  | translate (MoreEq (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.CmpGe (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Not (a)) = let
      val (code1,arg1) = evalArg a
      val l = makenextlabel ()
    in
      (l,[LLVM.Xor (l,LLVM.i1,(LLVM.Num 1),arg1)])
    end
  | translate (Plus (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.Add (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Minus (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.Sub (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Mult (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.Mul (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Div (a,b)) = let
      val (code1,arg1) = evalArg a
      val (code2,arg2) = evalArg b
      val l = makenextlabel ()
    in
      (l,code1@code2@[LLVM.Div (l,LLVM.i32,arg1,arg2)])
    end
  | translate (Apply ((Var v),exps)) =  let
      val argsAndCodes = map evalArg exps
      val code = (foldr (op @) [] (map (#1) argsAndCodes))
      val args = (map (#2) argsAndCodes)
      val l = makenextlabel ()
    in
      (l,code@[LLVM.Call (l,LLVM.i32,v,args)])
    end
  | translate (Apply _) =  raise (TranslationError "Can only apply on variables")
  | translate (If (bexp,texp,fexp)) = let
      val [l1,l2,l3,l4] = map makenextlabel [(),(),(),()]
      val (bcode,bres) = evalArg bexp
      val (tcode,tres) = evalArg texp
      val (fcode,fres) = evalArg fexp
    in
      (l4, bcode@[
          LLVM.CndBr (bres,(LLVM.Label l1),(LLVM.Label l2))
        , LLVM.DefnLabel l1
      ]@tcode@[
          LLVM.Add (l4,LLVM.i32,tres,(LLVM.Num 0))
        , LLVM.Br (LLVM.Label l3)
        , LLVM.DefnLabel l2
      ]@fcode@[
          LLVM.Add (l4,LLVM.i32,fres,(LLVM.Num 0))
        , LLVM.DefnLabel l3
      ])
    end
  | translate (Let (id,exp,inexp)) = let
      val (vcode,varg) = evalArg exp
      val (code,res) = evalArg inexp
    in
      (res, vcode@[LLVM.Store (LLVM.i32,varg,(LLVM.Variable id))]@code)
    end
  | translate (LetSta (fid,xids,fexp,inexp)) = let
      val l = makenextlabel ()
    in
      test_error ([
          sayopt1 "jmp" l
        , saylabel fid ] @
        (map (sayopt1 "popvar") xids) @ [
          translate fexp
        , saylabel l
        , translate inexp
      ])
    end
  | translate (LetDyn (fid,xids,fexp,inexp)) = let
      val l = makenextlabel ()
    in
      test_error ([
          sayopt1 "jmp" l
        , saylabel fid ] @
        (map (sayopt1 "popvar") xids) @ [
          translate fexp
        , saylabel l
        , translate inexp
      ])
    end

end
