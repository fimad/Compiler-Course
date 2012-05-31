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
"print"  => (Tokens.PRINT(!pos,!pos));
"dim"    => (Tokens.DIM(!pos,!pos));
"and"    => (Tokens.AND(!pos,!pos));
"or"     => (Tokens.OR(!pos,!pos));
"for"    => (Tokens.FOR(!pos,!pos));
"to"     => (Tokens.TO(!pos,!pos));
"by"     => (Tokens.BY(!pos,!pos));
"do"     => (Tokens.DO(!pos,!pos));
"if"     => (Tokens.IF(!pos,!pos));
"then"   => (Tokens.THEN(!pos,!pos));
"else"   => (Tokens.ELSE(!pos,!pos));
"end"    => (Tokens.END(!pos,!pos));
"let"    => (Tokens.LET(!pos,!pos));
"fun" => (Tokens.FUN(!pos,!pos));
"in" => (Tokens.IN(!pos,!pos));
"pass" => (Tokens.INT(0,!pos,!pos));
"true" => (Tokens.BOOL(true,!pos,!pos));
"false" => (Tokens.BOOL(false,!pos,!pos));
{digit}+\.{digit}* => (Tokens.FLOAT ( ((fn (l,r,_) => l+r)(foldr (fn(a,(left,right,point))=>
            if a = #"." then
              (left,right,true)
            else
              if point then
                (left,(real (ord(a)-ord(#"0")))+(right / 10.0), point)
              else
                ((real (ord(a)-ord(#"0")))+(left*10.0), right, point)
          )
          (0.0,0.0,false) (rev (explode yytext)))),!pos,!pos));
{digit}+ => (Tokens.INT (foldr (fn(a,r)=>ord(a)-ord(hd (explode "0"))+(r*10)) 0 (rev (explode yytext)),!pos,!pos));
{id_start}{id_main}* => (Tokens.ID (yytext,!pos,!pos));
";"      => (Tokens.SEMICOLON(!pos,!pos));
"~"      => (Tokens.NEG(!pos,!pos));
")"      => (Tokens.RPAREN(!pos,!pos));
"("      => (Tokens.LPAREN(!pos,!pos));
":="     => (Tokens.ASSIGN(!pos,!pos));
"="      => (Tokens.EQ(!pos,!pos));
"+"      => (Tokens.PLUS(!pos,!pos));
"-"      => (Tokens.MINUS(!pos,!pos));
"/"      => (Tokens.DIV(!pos,!pos));
"*"      => (Tokens.MULT(!pos,!pos));
","      => (Tokens.COMMA(!pos,!pos));
"!"      => (Tokens.NOT(!pos,!pos));
"<"      => (Tokens.LESS(!pos,!pos));
"<="     => (Tokens.LESSEQ(!pos,!pos));
">"      => (Tokens.MORE(!pos,!pos));
">="     => (Tokens.MOREEQ(!pos,!pos));
"[]"     => (Tokens.EMPTY_ARRAY(!pos,!pos));
"["      => (Tokens.START_ARRAY(!pos,!pos));
"]"      => (Tokens.END_ARRAY(!pos,!pos));
"#"      => (Tokens.POUND(!pos,!pos));
.        => (error ("calc: ignoring bad character "^yytext); lex());
