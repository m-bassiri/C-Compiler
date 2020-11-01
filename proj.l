%{
  #include "proj.tab.h"
%}

%option noyywrap

%%
[0-9]+	{yylval.num = atoi(yytext); return NUM_;}
"=="    {yylval.op = strdup(yytext); return EQ_;}
"!="    {yylval.op = strdup(yytext); return NEQ_;}
"<="    {yylval.op = strdup(yytext); return LEQ_;}
">="    {yylval.op = strdup(yytext); return GEQ_;}
"&&"    {yylval.op = strdup(yytext); return LOGAND_;}
"||"    {yylval.op = strdup(yytext); return LOGOR_;}
"+"     {yylval.op = strdup(yytext); return '+';}
"*"     {yylval.op = strdup(yytext); return '*';}
"-"     {yylval.op = strdup(yytext); return '-';}
"/"     {yylval.op = strdup(yytext); return '/';}
"="     {yylval.op = strdup(yytext); return '=';}
"("     {yylval.op = strdup(yytext); return '(';}
")"     {yylval.op = strdup(yytext); return ')';}
"!"     {yylval.op = strdup(yytext); return '!';}
"~"     {yylval.op = strdup(yytext); return '~';}
"&"     {yylval.op = strdup(yytext); return '&';}
"|"     {yylval.op = strdup(yytext); return '|';}
"{"     {yylval.op = strdup(yytext); return '{';}
"}"     {yylval.op = strdup(yytext); return '}';}
"["     {yylval.op = strdup(yytext); return '[';}
"]"     {yylval.op = strdup(yytext); return ']';}
">"     {yylval.op = strdup(yytext); return '>';}
"<"     {yylval.op = strdup(yytext); return '<';}
"^"     {yylval.op = strdup(yytext); return '^';}
";"     {yylval.op = strdup(yytext); return ';';}
","     {yylval.op = strdup(yytext); return ',';}
"int"	{yylval.keyword = strdup(yytext); return INT_;}
"void"	{yylval.keyword = strdup(yytext); return VOID_;}
"if"	{yylval.keyword = strdup(yytext); return IF_;}
"else"	{yylval.keyword = strdup(yytext); return ELSE_;}
"while"	{yylval.keyword = strdup(yytext); return WHILE_;}
"for"	{yylval.keyword = strdup(yytext); return FOR_;}
"main"	{yylval.keyword = strdup(yytext); return MAIN_;}
"return"	{yylval.keyword = strdup(yytext); return RETURN_;}
[A-Za-z_][A-Za-z_0-9]*	{yylval.id = strdup(yytext); return ID_;}
[\n \t]	;
.	;
%%
	
