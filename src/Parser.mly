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
%token SEMICOLON COMMA
%token LET OBSERVE FLIP LBRACE RBRACE FST SND

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
%left NEG
/* entry point */

%start program
%type <ExternalGrammar.eexpr> program

%%

expr:
    | LPAREN expr RPAREN { $2 }
    | TRUE { True }
    | FALSE { False }
    | INT LPAREN; sz=INT_LIT; COMMA; value=INT_LIT; RPAREN  { Int(sz, value) }
    | DISCRETE LPAREN; args=separated_list(COMMA, FLOAT_LIT); RPAREN { Discrete(args) }
    | expr EQUAL_TO expr { Eq($1, $3) }
    | expr PLUS expr { Plus($1, $3) }
    | LPAREN expr COMMA expr RPAREN { Tup($2, $4) }
    | FST expr { Fst($2) }
    | SND expr { Snd($2) }
    | ID { Ident($1) }
    | expr AND expr { And($1, $3) }
    | expr OR expr { Or($1, $3) }
    | NOT expr { Not($2) }
    | FLIP FLOAT_LIT { Flip($2) }
    | OBSERVE expr { Observe($2) }
    | IF expr THEN expr ELSE expr { Ite($2, $4, $6) }
    | LET ID EQUAL expr IN expr { Let($2, $4, $6) }


program:
  expr EOF { $1 }

