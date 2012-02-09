(* Will Coster *)

(*these are tokens, prefixed with t for token*)
datatype lexresult 
  = tID of string
  | tNum of int
  | tEqual
  | tPlus
  | tMinus
  | tDiv
  | tMult
  | tLet
  | tIn
  | tLetSta
  | tLetDyn
  | tLParen
  | tRParen
  | EOF

(*called when the lexer finishes*)
val eof = fn () => EOF

(*error reporting*)
val error = fn x => print(x ^ "\n")

val linenum = ref 1

%%

%structure EvalLex
id_start=[A-Za-z];
id_main=[A-Za-z_0-9];
digit=[0-9];
ws = [\ \t\n];

%%
{ws}+    => (lex());
"let"    => (tLet);
"letsta" => (tLetSta);
"letdyn" => (tLetDyn);
"in" => (tIn);
{digit}+ => (tNum (foldr (fn(a,r)=>ord(a)-ord(hd (explode "0"))+(r*10)) 0 (explode yytext)));
{id_start}{id_main}* => (tID yytext);
")"      => (tRParen);
"("      => (tLParen);
"="      => (tEqual);
"+"      => (tPlus);
"-"      => (tMinus);
"/"      => (tDiv);
"*"      => (tMult);
.        => (error ("calc: ignoring bad character "^yytext); lex());
