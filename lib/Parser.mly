%{
  open ExternalGrammar
  open Bignum
%}

/* Tokens */
%token EOF
%token PLUS MINUS MULTIPLY DIVIDE MODULUS
%token LT LTE GT GTE EQUAL_TO NEQ EQUAL LEFTSHIFT RIGHTSHIFT
%token AND OR NOT DISCRETE IFF XOR SAMPLE
%token LPAREN RPAREN
%token IF THEN ELSE TRUE FALSE IN INT
%token SEMICOLON COMMA COLON
%token LET OBSERVE FLIP LBRACE RBRACE FST SND FUN BOOL ITERATE UNIFORM BINOMIAL
%token LIST LBRACKET RBRACKET CONS HEAD TAIL LENGTH

%token <int>    INT_LIT
%token <string> FLOAT_LIT
%token <string> ID

/* associativity rules */
%left OR
%left AND
%left NOT
%left IFF
%left XOR
%left LTE GTE LT GT NEQ
%right CONS
%left PLUS MINUS EQUAL_TO LEFTSHIFT RIGHTSHIFT
%left MULTIPLY DIVIDE MODULUS
/* entry point */

%start program
%type <ExternalGrammar.program> program

%%
num:
    | FLOAT_LIT { (Bignum.of_string $1) }
    | INT_LIT { (Bignum.of_int $1) }
    | INT_LIT DIVIDE INT_LIT { Bignum.($1 // $3) }

expr:
    | delimited(LPAREN, expr, RPAREN) { $1 }
    | TRUE { True({startpos=$startpos; endpos=$endpos}) }
    | FALSE { False({startpos=$startpos; endpos=$endpos}) }
    | INT delimited(LPAREN, separated_pair(INT_LIT, COMMA, INT_LIT), RPAREN)
        { Int({startpos=$startpos; endpos=$endpos}, fst $2, snd $2) }
    | DISCRETE delimited(LPAREN, separated_list(COMMA, num), RPAREN)
        { Discrete({startpos=$startpos; endpos=$endpos}, $2) }
    | SAMPLE expr { Sample({startpos=$startpos; endpos=$endpos}, $2) }
    | expr EQUAL_TO expr { Eq({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr RIGHTSHIFT INT_LIT { RightShift({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | expr LEFTSHIFT INT_LIT { LeftShift({startpos=$startpos; endpos=$endpos}, $1, $3) }
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
    | FLIP num { Flip({startpos=$startpos; endpos=$endpos}, $2) }
    | FLIP LPAREN num RPAREN { Flip({startpos=$startpos; endpos=$endpos}, $3) }
    | OBSERVE expr { Observe({startpos=$startpos; endpos=$endpos}, $2) }
    | IF expr THEN expr ELSE expr { Ite({startpos=$startpos; endpos=$endpos}, $2, $4, $6) }
    | ITERATE LPAREN id=ID COMMA e=expr COMMA k=INT_LIT RPAREN { Iter({startpos=$startpos; endpos=$endpos}, id, e, k) }
    | LET ID EQUAL expr IN expr { Let({startpos=$startpos; endpos=$endpos}, $2, $4, $6) }
    | delimited(LBRACKET, separated_nonempty_list(COMMA, expr), RBRACKET)
        { ListLit({startpos=$startpos; endpos=$endpos}, $1) }
    | LBRACKET RBRACKET typ_annot { ListLitEmpty({startpos=$startpos; endpos=$endpos}, $3) }
    | expr CONS expr { Cons({startpos=$startpos; endpos=$endpos}, $1, $3) }
    | HEAD expr { Head({startpos=$startpos; endpos=$endpos}, $2) }
    | TAIL expr { Tail({startpos=$startpos; endpos=$endpos}, $2) }
    | LENGTH expr { Length({startpos=$startpos; endpos=$endpos}, $2) }
    | UNIFORM LPAREN sz=INT_LIT COMMA b=INT_LIT COMMA e=INT_LIT RPAREN { Unif ({startpos=$startpos; endpos=$endpos}, sz, b, e)}
    | BINOMIAL LPAREN sz=INT_LIT COMMA n=INT_LIT COMMA p=num RPAREN { Binom({startpos=$startpos; endpos=$endpos}, sz, n, p)}

typ:
    | BOOL { TBool }
    | INT LPAREN; sz=INT_LIT; RPAREN  { TInt(sz) }
    | LPAREN typ COMMA typ RPAREN { TTuple($2, $4) }
    | LIST LPAREN typ RPAREN { TList($3) }

typ_annot: COLON typ { $2 }

arg: ID typ_annot { ($1, $2) }

func: FUN; name=ID; LPAREN; args=separated_list(COMMA, arg); RPAREN; return_type=option(typ_annot); LBRACE; body=expr; RBRACE
         { { name=name; args=args; return_type=return_type; body=body } }

program:
  funcs=list(func); body=expr; EOF { { functions=funcs; body=body } }

