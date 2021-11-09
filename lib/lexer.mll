{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }


}

let int = '-'? ['0'-'9'] ['0'-'9']*
let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token =
    parse
    | white                     { token lexbuf; }
    | newline                   { next_line lexbuf; token lexbuf }
    | '+'                       { PLUS }
    | '-'                       { MINUS }
    | '*'                       { MULTIPLY }
    | '/'                       { DIVIDE }
    | "<=>"                     { IFF }
    | "^"                       { XOR }
    | '%'                       { MODULUS }
    | '<'                       { LT }
    | '>'                       { GT }
    | '!'                       { NOT }
    | "int"                     { INT }
    | "bool"                    { BOOL }
    | "list"                    { LIST }
    | "<="                      { LTE }
    | ">="                      { GTE }
    | "=="                      { EQUAL_TO }
    | "<<"                      { LEFTSHIFT }
    | ">>"                      { RIGHTSHIFT }
    | "="                       { EQUAL }
    | "!="                      { NEQ }
    | "&&"                      { AND }
    | "||"                      { OR }
    | "::"                      { CONS }
    | "//"                      { comment lexbuf; }
    | "if"                      { IF }
    | "sample"                  { SAMPLE }
    | "else"                    { ELSE }
    | "discrete"                { DISCRETE }
    | "then"                    { THEN }
    | "true"                    { TRUE }
    | "false"                   { FALSE }
    | "let"                     { LET }
    | "fst"                     { FST }
    | "snd"                     { SND }
    | "in"                      { IN }
    | "iterate"                 { ITERATE }
    | "uniform"                 { UNIFORM }
    | "binomial"                { BINOMIAL }
    | "observe"                 { OBSERVE }
    | "flip"                    { FLIP }
    | "fun"                     { FUN }
    | "head"                    { HEAD }
    | "tail"                    { TAIL }
    | "length"                  { LENGTH }
    | '('                       { LPAREN }
    | ')'                       { RPAREN }
    | '['                       { LBRACKET }
    | ']'                       { RBRACKET }
    | '{'                       { LBRACE }
    | '}'                       { RBRACE }
    | ';'                       { SEMICOLON }
    | ':'                       { COLON }
    | ','                       { COMMA }
    | int as i                  { INT_LIT(int_of_string i); }
    | float as num              { FLOAT_LIT(num); }
    | id as ident               { ID(ident); }
    | eof                       { EOF }
and comment =
    parse
    | '\n'                      { token lexbuf }
    | _                         { comment lexbuf }
