(* Will Coster *)

structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0

(*called when the lexer finishes*)
val eof = fn () => Tokens.EOF(!pos,!pos)

(*error reporting*)
val error = fn x => print(x ^ "\n")

%%

%header (functor EvalLexFun(structure Tokens: Eval_TOKENS));
id_start=[A-Za-z];
id_main=[A-Za-z_0-9];
digit=[0-9];
ws = [\ \t];

%%
\n       => (pos := (!pos) + 1; lex());
{ws}+    => (lex());
"let"    => (Tokens.LET(!pos,!pos));
"letsta" => (Tokens.LETSTA(!pos,!pos));
"letdyn" => (Tokens.LETDYN(!pos,!pos));
"in" => (Tokens.IN(!pos,!pos));
{digit}+ => (Tokens.NUM (foldr (fn(a,r)=>ord(a)-ord(hd (explode "0"))+(r*10)) 0 (explode yytext),!pos,!pos));
{id_start}{id_main}* => (Tokens.ID (yytext,!pos,!pos));
")"      => (Tokens.RPAREN(!pos,!pos));
"("      => (Tokens.LPAREN(!pos,!pos));
"="      => (Tokens.EQ(!pos,!pos));
"+"      => (Tokens.PLUS(!pos,!pos));
"-"      => (Tokens.MINUS(!pos,!pos));
"/"      => (Tokens.DIV(!pos,!pos));
"*"      => (Tokens.MULT(!pos,!pos));
","      => (Tokens.COMMA(!pos,!pos));
.        => (error ("calc: ignoring bad character "^yytext); lex());
