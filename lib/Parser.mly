%{
  open ExternalGrammar
%}

/* Tokens */
%token EOF
%token PLUS MINUS MULTIPLY DIVIDE MODULUS
%token LT LTE GT GTE EQUAL_TO NEQ EQUAL
%token AND OR NOT DISCRETE IFF XOR
%token LPAREN RPAREN
%token IF THEN ELSE TRUE FALSE IN INT
%token SEMICOLON COMMA COLON
%token LET OBSERVE FLIP LBRACE RBRACE FST SND FUN BOOL ITERATE

%token <int>    INT_LIT
%token <float>  FLOAT_LIT
%token <string> ID

/* associativity rules */
%left OR
%left AND
%left NOT
%left IFF
%left XOR
%left LTE GTE LT GT NEQ
%left PLUS MINUS EQUAL_TO
%left MULTIPLY DIVIDE MODULUS
/* entry point */

%start program
%type <ExternalGrammar.program> program

%%

expr:
    | delimited(LPAREN, expr, RPAREN) { $1 }
    | TRUE { True({startpos=$startpos; endpos=$endpos}) }
    | FALSE { False({startpos=$startpos; endpos=$endpos}) }
    | INT delimited(LPAREN, separated_pair(INT_LIT, COMMA, INT_LIT), RPAREN)
        { Int({startpos=$startpos; endpos=$endpos}, fst $2, snd $2) }
    | DISCRETE delimited(LPAREN, separated_list(COMMA, FLOAT_LIT), RPAREN)
        { Discrete({startpos=$startpos; endpos=$endpos}, $2) }
    | expr EQUAL_TO expr { Eq({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr PLUS expr { Plus({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr MINUS expr { Minus({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr MULTIPLY expr { Mult({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr DIVIDE expr { Div({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr LTE expr { Lte({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr GTE expr { Gte({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr LT expr { Lt({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr GT expr { Gt({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr NEQ expr { Neq({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | delimited(LPAREN, separated_pair(expr, COMMA, expr), RPAREN) { Tup({startpos=$startpos; endpos=$endpos}, fst $1, snd $1) }
    | FST expr { Fst({startpos=$startpos; endpos=$endpos}, $2) }
    | SND expr { Snd({startpos=$startpos; endpos=$endpos}, $2) }
    | ID { Ident({startpos=$startpos; endpos=$endpos}, $1) }
    | ID delimited(LPAREN, separated_list(COMMA, expr), RPAREN) { FuncCall({startpos=$startpos; endpos=$endpos}, $1, $2) }
    | expr AND expr { And({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr OR expr { Or({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr IFF expr { Iff({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr XOR expr { Xor({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | NOT expr { Not({startpos=$startpos; endpos=$endpos}, $2) }
    | FLIP FLOAT_LIT { Flip({startpos=$startpos; endpos=$endpos}, $2) }
    | FLIP LPAREN FLOAT_LIT RPAREN { Flip({startpos=$startpos; endpos=$endpos}, $3) }
    | OBSERVE expr { Observe({startpos=$startpos; endpos=$endpos}, $2) }
    | IF expr THEN expr ELSE expr { Ite({startpos=$startpos; endpos=$endpos}, $2, $4, $6) }
    | ITERATE LPAREN id=ID COMMA e=expr COMMA k=INT_LIT RPAREN { Iter({startpos=$startpos; endpos=$endpos}, id, e, k) }
    | LET ID EQUAL expr IN expr { Let({startpos=$startpos; endpos=$endpos}, $2, $4, $6) }

typ:
    | BOOL { TBool }
    | INT LPAREN; sz=INT_LIT; RPAREN  { TInt(sz) }
    | LPAREN typ COMMA typ RPAREN { TTuple($2, $4) }

arg: ID COLON typ { ($1, $3) }

func: FUN; name=ID; LPAREN; args=separated_list(COMMA, arg); RPAREN LBRACE; body=expr; RBRACE
         { { name=name; args=args; body=body } }

program:
  funcs=list(func); body=expr; EOF { { functions=funcs; body=body } }

