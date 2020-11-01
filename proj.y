%{
#include <iostream>
#include <stdio.h>
#include <map>
#include <set>
#include <string.h>
#include <string>
#include <math.h>
#include <fstream>

using namespace std;
int yyparse();
extern FILE* yyin;
extern int yylex();
void yyerror(const char* error);

map<string,int> vals;
map<string,int> offsets;
set<string> arraysName;
set<string> funcsName;

ofstream out;

char pb[500][100];
char globalDataPb[100][100];
char globalValPb[100][100];
int i = 1,numberOfGlobalData = 0, k = 0;
int arg_idx = 1;
int cur_offset = 0;
int if_cnt = 1,ifStackPointer = 0;
int ifStack[10];
int while_cnt = 1,whileStackPointer = 0;
int whileStack[10];
int for_cnt = 1,forStackPointer = 0;
int forStack[10];
int v1;
bool allowed = true;

int scopeTree[50]={-1};
int currentScope=0,scopeCount = 0;
bool isVariableDeclareBeforeScope = false;

void declareVariable(const char* id){
	char buffer[10];
	if(isVariableDeclareBeforeScope)
		sprintf(buffer,"-%d",scopeCount+1);
	else
		sprintf(buffer,"-%d",currentScope);
	string idName = id;
	idName = idName + buffer;
	if(offsets.count(idName)!=0){
		char buffer[100];
		sprintf(buffer,"redeclaration of %s",id);
		yyerror(buffer);
	}
	offsets[idName]=cur_offset;
	vals[idName]=0;
	cur_offset+=4;
}

int getScopeNumber(const char* id){
	int scope = currentScope;
	if(isVariableDeclareBeforeScope)
		scope = scopeCount+1;
	string idName = id;
	while(scope != -1){
		char buffer[10];
		sprintf(buffer,"-%d",scope);
		if(offsets.count(idName+buffer)>0)
			return scope;
		scope = scopeTree[scope];	
	}
	char buffer[100];
	sprintf(buffer,"'%s' was not declared in this scope!",id);
	yyerror(buffer);
}

string getNameWithScope(const char* id){
	char buffer[10];
	sprintf(buffer,"-%d",getScopeNumber(id));
	return string(id)+buffer;
}
void declareArray(const char* id,int size){
	if(size<=0){
		char buffer[100];
		sprintf(buffer,"size of array '%s' is invalid!",id);
		yyerror(buffer);
	}
	sprintf(pb[i++],"addi $t0,$sp,4");
	sprintf(pb[i++],"push $t0");
	declareVariable(id);
	
	sprintf(pb[i++],"li $t0,$t1");
	sprintf(pb[i++],"addi $t0,$t0,-1");
	sprintf(pb[i++],"push $zero");
	sprintf(pb[i++],"bne $zero,$t0,-2");
	cur_offset+=4*size;
	arraysName.insert(getNameWithScope(id));		
}

%}


%union{
	char *id;
	char *keyword;
	int num;
	char *op;
	char *nt;
}

%token <id> ID_
%token <num> NUM_
%token <keyword> INT_
%token <keyword> VOID_
%token <keyword> IF_
%token <keyword> ELSE_
%token <keyword> WHILE_
%token <keyword> FOR_
%token <keyword> MAIN_
%token <keyword> RETURN_
%token <op> LOGAND_
%token <op> LOGOR_
%token <op> EQ_
%token <op> NEQ_
%token <op> LEQ_
%token <op> GEQ_
%left '['
%left ']'
%left '('
%left ')'
%left '{'
%left '}'
%left '='
%left '>'
%left '<'
%left '&'
%left '|'
%left '^'
%left ';'
%left '!'
%left '~'
%left '+'
%left '-'
%left '*'
%left '/'
%left ','

%type <nt> PROG
%type <nt> DEC
%type <nt> MAIN
%type <nt> VAR_DEC
%type <nt> FUNC_DEC
%type <nt> TYPE
%type <nt> ID_LIST
%type <nt> FUNC_IN_LIST
%type <nt> SCOPE
%type <nt> STMTS
%type <nt> STMT
%type <nt> FOR
%type <nt> IF
%type <nt> WHILE
%type <nt> STMT_DEC
%type <nt> STMT_ASGN
%type <nt> STMT_RET
%type <num> EXP
%type <nt> STMT_DEC_IDS
%type <nt> OP1
%type <nt> OP2
%type <nt> OP3
%type <nt> OP4
%type <nt> OP5
%type <nt> OP6
%type <num> TEMP1
%type <num> TEMP2
%type <num> TEMP3
%type <num> TEMP4
%type <num> TEMP5
%type <num> CALL_FUNC
%type <nt> CALL_FUNC_ID_LIST
%type <num> R

%%
PROG:		DEC MAIN			{sprintf(pb[0],"j main");
						if(numberOfGlobalData!=0){
							sprintf(globalDataPb[0],".data");
							for(int j=0;j<=numberOfGlobalData;j++)
								out << globalDataPb[j] << endl;
							for(int j=0;j<k;j++)
								out << globalValPb[j] << endl;
						}
						for(int j = 0; j < i; j++)
							out << pb[j] << endl;
						cout << "Compiled Successfully!\n";}
		| MAIN 				{sprintf(pb[0],"j main");
						for(int j = 0; j < i; j++)
							out << pb[j] << endl;
						cout << "Compiled Successfully!\n";}
		;
DEC:		DEC VAR_DEC
		| DEC FUNC_DEC
		| FUNC_DEC
		| VAR_DEC
		;
VAR_DEC:	TYPE ID_LIST ';'
		;
TYPE:		INT_
		| VOID_
		;
ID_LIST:	ID_LIST ',' ID_			{declareVariable($3);
						sprintf(globalDataPb[1+numberOfGlobalData++],"%s\t.word\t%d",$3,(numberOfGlobalData)*4);}
		| ID_LIST ',' ID_ '=' EXP 	{declareVariable($3);
						if(allowed) vals[getNameWithScope($3)] = $5;
						sprintf(globalDataPb[1+numberOfGlobalData++],"%s\t.word\t%d",$3,(numberOfGlobalData)*4);
						sprintf(globalValPb[k++],"sw $t1,%s($gp)",$3);}
		| ID_ 				{declareVariable($1);
						sprintf(globalDataPb[1+numberOfGlobalData++],"%s\t.word\t%d",$1,(numberOfGlobalData)*4);}
		| ID_ '=' EXP			{declareVariable($1);
						if(allowed) vals[getNameWithScope($1)] = $3;
						sprintf(globalDataPb[1+numberOfGlobalData++],"%s\t.word\t%d",$1,(numberOfGlobalData)*4);
						sprintf(globalValPb[k++],"sw $t1,%s($gp)",$1);}
		;

FUNC_DEC:	TYPE ID_			{if(funcsName.find($2)!=funcsName.end()){
							char buffer[100];
							sprintf(buffer,"redeclaration of function %s",$2);
							yyerror(buffer);
						}
						sprintf(pb[i++],"%s : ",$2);
						isVariableDeclareBeforeScope=true;}
		'(' FUNC_IN_LIST ')' 		{funcsName.insert($2);
						arg_idx = 1;
						isVariableDeclareBeforeScope=false;}
		SCOPE
		;
FUNC_IN_LIST:	FUNC_IN_LIST ',' TYPE ID_		{sprintf(pb[i++],"push $a%d",arg_idx++);
							declareVariable($4);}
		| TYPE ID_				{sprintf(pb[i++],"push $a%d",arg_idx++);
							declareVariable($2);}
		| FUNC_IN_LIST ',' TYPE ID_ '[' ']'	{sprintf(pb[i++],"push $a%d",arg_idx++);
							declareVariable($4);
							arraysName.insert(getNameWithScope($4));}
		| TYPE ID_ '[' ']'			{sprintf(pb[i++],"push $a%d",arg_idx++);
							declareVariable($2);
							arraysName.insert(getNameWithScope($2));}	
		|				
		;
MAIN:		TYPE MAIN_ '(' ')' 			{sprintf(pb[i++],"%s","main:");}
		SCOPE		
		;
SCOPE:		'{' 					{scopeCount++;
							scopeTree[scopeCount] = currentScope;
							currentScope = scopeCount;}
		'}'					{currentScope = scopeTree[currentScope];}
		| '{' 					{scopeCount++;
							scopeTree[scopeCount] = currentScope;
							currentScope = scopeCount;
							}
		STMTS
		'}'					{currentScope = scopeTree[currentScope];}
		;
STMTS:		STMTS STMT
		| STMT
		;
STMT:		SCOPE
		| FOR
		| IF
		| WHILE
		| STMT_DEC ';'
		| STMT_ASGN ';'
		| STMT_RET ';'
		| CALL_FUNC ';'
		;
FOR:		FOR_ 					{isVariableDeclareBeforeScope=true;} 
		'(' FOR_START ';'			{sprintf(pb[i++],"startFor%d:",for_cnt);}	
		EXP ';'					{sprintf(pb[i++],"beq $t1,$zero,endFor%d",for_cnt);
							sprintf(pb[i++],"j startForScope%d",for_cnt);
							sprintf(pb[i++],"forAssignment%d:",for_cnt);}
		STMT_ASGN ')' 				{isVariableDeclareBeforeScope=false;
							sprintf(pb[i++],"j startFor%d",for_cnt);
							sprintf(pb[i++],"startForScope%d:",for_cnt);
							forStack[forStackPointer++] = for_cnt++;}
		SCOPE 					{sprintf(pb[i++],"j forAssignment%d",forStack[--forStackPointer]);
							sprintf(pb[i++],"endFor%d:",forStack[forStackPointer]);}
		;
FOR_START:	STMT_DEC
		| STMT_ASGN
		;		

IF:		IF_ '(' EXP ')' 			{sprintf(pb[i++],"beq $t1,$zero,else%d",if_cnt);
							ifStack[ifStackPointer++] = if_cnt++;
							allowed = $3;}
		R
		;
R:		SCOPE					{sprintf(pb[i++],"else%d:",ifStack[--ifStackPointer]);
							allowed = true;}
		| SCOPE ELSE_ 				{sprintf(pb[i++],"else%d:",ifStack[--ifStackPointer]);
							allowed = !allowed;}
		SCOPE					{allowed = true;}
		;
		;
WHILE:		WHILE_ 			{sprintf(pb[i++],"while%d:",while_cnt);}
		'(' EXP ')'			{sprintf(pb[i++],"bne $t1,$zero,endwhile%d",while_cnt);
							whileStack[whileStackPointer++] = while_cnt++;}
		SCOPE					{
							sprintf(pb[i++],"j while%d",whileStack[--whileStackPointer]);
							sprintf(pb[i++],"endwhile%d:",whileStack[whileStackPointer]);}
		;
STMT_DEC:	TYPE STMT_DEC_IDS
		;
STMT_DEC_IDS:	STMT_DEC_IDS ',' ID_			{sprintf(pb[i++],"push $zero");
							declareVariable($3);}
		| STMT_DEC_IDS ',' ID_ '=' EXP 		{sprintf(pb[i++],"push $t1");
							declareVariable($3);
							if(allowed) vals[getNameWithScope($3)] = $5;}
		| ID_ 					{sprintf(pb[i++],"push $zero");
							declareVariable($1);}
		| ID_ '=' EXP 				{sprintf(pb[i++],"push $t1");
							declareVariable($1);
							if(allowed) vals[getNameWithScope($1)] =$3;}
		| ID_ '[' EXP ']'{declareArray($1,$3);}
		| STMT_DEC_IDS ',' ID_ '[' EXP ']'{declareArray($3,$5);}
		;
STMT_ASGN:	ID_ '=' EXP				{if(getScopeNumber($1)==0)
								sprintf(pb[i++],"sw $t1,%s($gp)",$1);
							else
								sprintf(pb[i++],"sw $t1,-%d($sp)",cur_offset-offsets[getNameWithScope($1)]);
							if(allowed) vals[getNameWithScope($1)]=$3;}			
		| ID_ '[' EXP 		{sprintf(pb[i++],"lw $t0,-%d($sp)",cur_offset-offsets[getNameWithScope($1)]);
							sprintf(pb[i++],"add $t1,$t0,$t1");
							sprintf(pb[i++],"push $t1");
							cur_offset+=4;
							}
		']' '=' EXP			{sprintf(pb[i++],"pop $t0");
							cur_offset-=4;
							sprintf(pb[i++],"pop $t0");
							sprintf(pb[i++],"sw $t1,0($t0)");
							}											
		;
STMT_RET:	RETURN_ EXP				{sprintf(pb[i++],"mov $v1,$t1");
							sprintf(pb[i++],"subi $sp,$sp,%d",cur_offset);
							v1 = $2;
							cur_offset = 0;
							sprintf(pb[i++],"jr $ra");}
		;
EXP:		EXP 					{sprintf(pb[i++],"mov $t2,$t1");}
		OP1 TEMP1				{sprintf(pb[i++],"mov $t3,$t1");
							if(!strcmp($3,"&")){
								sprintf(pb[i++],"and $t1,$t2,$t3");
								$$=$1&$4;
							}
							else if(!strcmp($3,"|")){
								sprintf(pb[i++],"or $t1,$t2,$t3");
								$$=$1|$4;
							}
							else if(!strcmp($3,"^")){
								sprintf(pb[i++],"xor $t1,$t2,$t3");
								$$=$1^$4;
							}
							else if(!strcmp($3,"&&")){
								sprintf(pb[i++],"sne $t2,$t2,$zero");
								sprintf(pb[i++],"sne $t3,$t3,$zero");
								sprintf(pb[i++],"and $t1,$t2,$t3");
								$$=$1&&$4;
							}
							else if(!strcmp($3,"||")){
								sprintf(pb[i++],"sne $t2,$t2,$zero");
								sprintf(pb[i++],"sne $t3,$t3,$zero");
								sprintf(pb[i++],"or $t1,$t2,$t3");
								$$=$1||$4;
							}}
		| TEMP1					{$$=$1;}
		;
TEMP1:		TEMP1 					{sprintf(pb[i++],"mov $t2,$t1");}
		OP2 TEMP2				{sprintf(pb[i++],"mov $t3,$t1");
							if(!strcmp($3,"==")){
								sprintf(pb[i++],"seq $t1,$t2,$t3");
								$$=($1==$4);
							}
							else if(!strcmp($3,"!=")){
								sprintf(pb[i++],"sne $t1,$t2,$t3");
								$$=($1!=$4);
							}}
		| TEMP2					{$$=$1;}
		;
TEMP2:		TEMP2 					{sprintf(pb[i++],"mov $t2,$t1");}
		OP3 TEMP3				{sprintf(pb[i++],"mov $t3,$t1");
							if(!strcmp($3,"<=")){
								sprintf(pb[i++],"sle $t1,$t2,$t3");
								$$=($1<=$4);
							}
							else if(!strcmp($3,"<")){
								sprintf(pb[i++],"slt $t1,$t2,$t3");
								$$=($1<$4);
							}
							else if(!strcmp($3,">=")){
								sprintf(pb[i++],"sge $t1,$t2,$t3");
								$$=($1>=$4);
							}
							else if(!strcmp($3,">")){
								sprintf(pb[i++],"sgt $t1,$t2,$t3");
								$$=($1>$4);
							}}
		| TEMP3					{$$=$1;}
		;
TEMP3:		TEMP3					{sprintf(pb[i++],"mov $t2,$t1");}
		OP4 TEMP4				{sprintf(pb[i++],"mov $t3,$t1");
							if(!strcmp($3,"+")){
								sprintf(pb[i++],"add $t1,$t2,$t3");
								$$=($1+$4);
							}
							else if(!strcmp($3,"-")){
								sprintf(pb[i++],"sub $t1,$t2,$t3");
								$$=($1-$4);
							}}
		| TEMP4					{$$=$1;}
		;
TEMP4:		TEMP4 					{sprintf(pb[i++],"mov $t2,$t1");}
		OP5 TEMP5				{sprintf(pb[i++],"mov $t3,$t1");
							if(!strcmp($3,"*")){
								sprintf(pb[i++],"mul $t1,$t2,$t3");
								$$=($1*$4);
							}
							else if(!strcmp($3,"/")){
								if($4==0){
									yyerror("division by zero buddy!");
								} 
								sprintf(pb[i++],"div $t1,$t2,$t3");
								$$=($1/$4);
							}}
		| TEMP5					{$$=$1;}
		;
TEMP5:		'(' EXP ')'				{$$=$2;}
		| OP6 TEMP5				{sprintf(pb[i++],"mov $t2,$t1");
							if(!strcmp($1,"-")){
								sprintf(pb[i++],"sub $t1,$zero,$t2");
								$$= -$2;
							}
							else if(!strcmp($1,"~")){
								sprintf(pb[i++],"nor $t1,$t2,$t2");
								$$= ~$2;
							}
							else if(!strcmp($1,"!")){
								sprintf(pb[i++],"sne $t2,$t2,$zero");
								sprintf(pb[i++],"nor $t1,$t2,$t2");
								$$= !$2;
							}}
		| ID_				{
								if(getScopeNumber($1)==0)
									sprintf(pb[i++],"lw $t1,%s($gp)",$1);
								else
									sprintf(pb[i++],"lw $t1,-%d($sp)",cur_offset-offsets[getNameWithScope($1)]);
								$$=vals[getNameWithScope($1)];
							}
		| ID_ '[' EXP ']'	{
								if(arraysName.count(getNameWithScope($1))==0){
								yyerror("invalid type for array subscript!");
								}
								sprintf(pb[i++],"lw $t0,-%d($sp)",cur_offset-offsets[getNameWithScope($1)]);
								sprintf(pb[i++],"add $t1,$t0,$t1");
								sprintf(pb[i++],"lw $t1,0($t1)");
							}

		| NUM_					{sprintf(pb[i++],"li $t1,%d",$1);
							$$=$1;}
		| CALL_FUNC				{sprintf(pb[i++],"mov $t1,$v1");
							$$=v1;}
		;
CALL_FUNC:	ID_ '(' CALL_FUNC_ID_LIST ')'		{if(funcsName.find($1)==funcsName.end()){
								char buffer[100];
								sprintf(buffer,"function '%s' doesn't exist!",$1);
								yyerror(buffer);
							}
							sprintf(pb[i++],"jal %s",$1);
							arg_idx = 1;}
		| ID_ '(' ')'				{if(funcsName.find($1)==funcsName.end()){
								char buffer[100];
								sprintf(buffer,"function '%s' doesn't exist!",$1);
								yyerror(buffer);
							}
							sprintf(pb[i++],"jal %s",$1);
							arg_idx = 1;}
		;
CALL_FUNC_ID_LIST:	CALL_FUNC_ID_LIST ',' EXP	{sprintf(pb[i++],"mov $a%d,$t1",arg_idx++);}
			| EXP				{sprintf(pb[i++],"mov $a%d,$t1",arg_idx++);}
			;
OP1:		LOGAND_
		| LOGOR_
		| '&'
		| '|'
		| '^'
		;
OP2:		EQ_
		| NEQ_
		;
OP3:		'<'
		| LEQ_
		| '>'
		| GEQ_
		;
OP4:		'+'
		| '-'
		;
OP5:		'*'
		| '/'
		;
OP6:		'!'
		| '-'
		| '~'
		;
%%
int main(int argc, char** argv){
	FILE* file = fopen(argv[1], "r");
	yyin = file;
	out.open("out.asm");
	yyparse();
	if(argc==3) if (!strcmp(argv[2],"--show")){
	cout << "Name-Scope\tValue\tStack Offset\n";
	map<string,int>::iterator it;
	for(it=vals.begin(); it!= vals.end();it++)
		cout << it->first << "\t\t" << it->second 
		<< '\t' << (offsets.find(it->first))->second << endl;
	}
	return 0;
}
void yyerror(const char* error){
	cout<<"Compile Error: "<<error<<endl;
	exit(-1);
}
