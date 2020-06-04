
(* This file was auto-generated based on "Parser.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
    match s with
    | 115 ->
        "Dangling expression.\n"
    | 59 ->
        "Dangling expression after '+'.\n"
    | 58 ->
        "Invalid or missing argument for '+'.\n"
    | 65 ->
        "Dangling expression after '||'.\n"
    | 64 ->
        "Invalid or missing argument for '||'.\n"
    | 67 ->
        "Dangling expression after '!='.\n"
    | 66 ->
        "Invalid or missing argument for '!='.\n"
    | 60 ->
        "Invalid or missing argument for '*'.\n"
    | 69 ->
        "Dangling expression after '-'.\n"
    | 68 ->
        "Invalid or missing argument for '-'.\n"
    | 73 ->
        "Dangling expression after '<='.\n"
    | 72 ->
        "Invalid or missing argument for '<='.\n"
    | 75 ->
        "Dangling expression after '<'.\n"
    | 74 ->
        "Dangling expression after '>='.\n"
    | 77 ->
        "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
    | 76 ->
        "Invalid or missing argument for '>='.\n"
    | 79 ->
        "Dangling expression after '>'.\n"
    | 78 ->
        "Invalid argument for '>'.\n"
    | 71 ->
        "Invalid '='.\n"
    | 70 ->
        "Invalid argument for '='.\n"
    | 62 ->
        "Invalid '/' (mistaken keyword usage? See reserved keywords.)\n"
    | 81 ->
        "Dangling expression after 'and'.\n"
    | 80 ->
        "Invalid 'and' (mistaken keyword usage? See reserved keywords.)\n"
    | 0 ->
        "Invalid program: missing main body.\n"
    | 107 ->
        "Dangling expression after 'snd'.\n"
    | 22 ->
        "Invalid 'snd' (mistaken keyword usage? See reserved keywords.)\n"
    | 106 ->
        "Dangling expression after 'observe'.\n"
    | 23 ->
        "Invalid 'observe' (mistaken keyword usage? See reserved keywords.)\n"
    | 105 ->
        "Dangling expression after 'not'.\n"
    | 24 ->
        "Invalid 'not' (mistaken keyword usage? See reserved keywords.).\n"
    | 100 ->
        "Invalid tuple declaration (missing ')'?)\n"
    | 103 ->
        "Invalid tuple declaration (missing ')'?)\n"
    | 102 ->
        "Invalid tuple declaration (missing ')'?)\n"
    | 25 ->
        "Dangling '(' (missing ')'?)\n"
    | 26 ->
        "Dangling 'let'.\n"
    | 27 ->
        "Invalid 'let' syntax (missing '='?)\n"
    | 97 ->
        "Invalid 'let' syntax (missing 'in'?)\n"
    | 99 ->
        "Dangling expression after 'let'.\n"
    | 98 ->
        "Invalid 'let' syntax.\n"
    | 28 ->
        "Invalid 'let' syntax (missing 'in'?).\n"
    | 29 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 30 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 31 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 93 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 94 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 95 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 32 ->
        "Invalid 'iterate' syntax (missing ')'?).\n"
    | 33 ->
        "Invalid 'int' declaration.\nNote: Int literals are not currently supported; the syntax for 'int' is 'int(size, value)'.\n"
    | 34 ->
        "Invalid 'int' declaration.\n"
    | 35 ->
        "Invalid 'int' declaration.\n"
    | 36 ->
        "Invalid 'int' declaration (missing ')'?)\n"
    | 37 ->
        "Invalid 'int' declaration (missing ')'?)\n"
    | 88 ->
        "Syntax error (missing 'then'?)\n"
    | 90 ->
        "Syntax error (missing 'else'?)\n"
    | 92 ->
        "Syntax error (improve me?).\n"
    | 91 ->
        "Use of reserved keyword.\n"
    | 89 ->
        "Invalid 'if' (missing 'then'?)\n"
    | 39 ->
        "Invalid 'if' (missing 'then'?).\n"
    | 40 ->
        "Invalid function call (missing ')'?)\n"
    | 85 ->
        "Invalid function call (missing ')'?)\n"
    | 86 ->
        "Invalid function call (missing ')'?)\n"
    | 41 ->
        "Invalid function call (missing ')'?)\n"
    | 1 ->
        "Invalid function declaration (missing identifier?).\n"
    | 2 ->
        "Invalid function declaration.\n"
    | 3 ->
        "Invalid function declaration.\n"
    | 19 ->
        "Missing function body (did you forget a '{'?)\n"
    | 108 ->
        "Dangling function declaration (did you forget a '}'?)\n"
    | 20 ->
        "Dangling function declaration.\n"
    | 117 ->
        "Invalid function declaration.\n"
    | 4 ->
        "Dangling function declaration.\n"
    | 5 ->
        "Dangling function declaration.\n"
    | 6 ->
        "Error in function declaration: extra \"(\"\n"
    | 12 ->
        "Error in function declaration: extra \"(\"\n"
    | 13 ->
        "Error in function declaration.\n"
    | 14 ->
        "Missing argument identifier.\n"
    | 7 ->
        "Dangling function declaration.\n"
    | 8 ->
        "Dangling function declaration.\n"
    | 9 ->
        "Dangling function declaration.\n"
    | 110 ->
        "Invalid function declaration.\n"
    | 111 ->
        "Dangling function declaration.\n"
    | 57 ->
        "Parse error.\n"
    | 42 ->
        "Dangling 'fst' declaration: expected argument.\n"
    | 43 ->
        "Dangling 'flip' declaration: expected argument.\n"
    | 44 ->
        "Dangling 'flip' declaration: expected argument.\n"
    | 45 ->
        "Dangling 'flip' declaration: expected ')'\n"
    | 49 ->
        "Dangling 'discrete' declaration: expected arguments.\n"
    | 50 ->
        "Dangling 'discrete' declaration.\n"
    | 51 ->
        "Dangling 'discrete' declaration (did you forget a ')'?).\n"
    | 52 ->
        "Dangling 'discrete' declaration (did you forget a ')'?).\n"
    | _ ->
        raise Not_found
