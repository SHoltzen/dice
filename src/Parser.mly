%{
  open ExternalGrammar
%}

/* Tokens */
%token EOF
%token PLUS MINUS MULTIPLY DIVIDE MODULUS
%token LT LTE GT GTE EQUAL_TO NEQ EQUAL
%token AND OR NOT DISCRETE
%token LPAREN RPAREN
%token IF THEN ELSE TRUE FALSE IN INT
%token SEMICOLON COMMA COLON
%token LET OBSERVE FLIP LBRACE RBRACE FST SND FUN BOOL

%token <int>    INT_LIT
%token <float>  FLOAT_LIT
%token <string> ID

/* associativity rules */
%left OR
%left AND
%left NOT
%left LTE GTE LT GT NEQ
%left PLUS MINUS EQUAL_TO
%left MULTIPLY DIVIDE MODULUS
/* entry point */

%start program
%type <ExternalGrammar.program> program

%%

expr:
    | delimited(LPAREN, expr, RPAREN) { $1 }
    | TRUE { True }
    | FALSE { False }
    | INT delimited(LPAREN, separated_pair(INT_LIT, COMMA, INT_LIT), RPAREN)  { Int(fst $2, snd $2) }
    | DISCRETE delimited(LPAREN, separated_list(COMMA, FLOAT_LIT), RPAREN) { Discrete($2) }
    | expr EQUAL_TO expr { Eq($1, $3) }
    | expr PLUS expr { Plus($1, $3) }
    | expr MINUS expr { Minus($1, $3) }
    | expr MULTIPLY expr { Mult($1, $3) }
    | expr DIVIDE expr { Div($1, $3) }
    | expr LTE expr { Lte($1, $3) }
    | expr GTE expr { Gte($1, $3) }
    | expr LT expr { Lt($1, $3) }
    | expr GT expr { Gt($1, $3) }
    | expr NEQ expr { Neq($1, $3) }
    | delimited(LPAREN, separated_pair(expr, COMMA, expr), RPAREN) { Tup(fst $1, snd $1) }
    | FST expr { Fst($2) }
    | SND expr { Snd($2) }
    | ID { Ident($1) }
    | ID delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { FuncCall($1, $2) }
    | expr AND expr { And($1, $3) }
    | expr OR expr { Or($1, $3) }
    | NOT expr { Not($2) }
    | FLIP FLOAT_LIT { Flip($2) }
    | FLIP LPAREN FLOAT_LIT RPAREN { Flip($3) }
    | OBSERVE expr { Observe($2) }
    | IF expr THEN expr ELSE expr { Ite($2, $4, $6) }
    | LET ID EQUAL expr IN expr { Let($2, $4, $6) }

typ:
    | BOOL { TBool }
    | INT LPAREN; sz=INT_LIT; RPAREN  { TInt(sz) }
    | LPAREN typ COMMA typ RPAREN { TTuple($2, $4) }

arg: ID COLON typ { ($1, $3) }

func: FUN; name=ID; LPAREN; args=separated_list(COMMA, arg); RPAREN LBRACE; body=expr; RBRACE
         { { name=name; args=args; body=body } }

program:
  funcs=list(func); body=expr; EOF { { functions=funcs; body=body } }

