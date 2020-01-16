open Core
open Lexing
open Lexer
open Parser

let eps = 0.00001

let assert_feq f1 f2 =
  OUnit2.assert_equal ~cmp:(fun x y ->
      (Float.compare (Float.abs (f1 -. f2)) eps) < 0) f1 f2
    ~printer:string_of_float

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


(** [parse_and_prob] parses and computes the probability for string [txt] *)
let parse_and_prob ?debug txt =
  let buf = Lexing.from_string txt in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith (Format.sprintf "Error parsing %s" txt)
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith (Format.sprintf "Error parsing %s" txt) in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
   | _ -> ());
  CoreGrammar.get_prob (CoreGrammar.from_external_prog parsed)

(** [dir_is_empty dir] is true, if [dir] contains no files except
 * "." and ".."
 *)
let dir_is_empty dir =
  Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
  *)
let dir_contents dir =
  let rec loop result = function
    | f::fs ->
      (match Sys.is_directory f with
       | `Yes ->
         Sys.readdir f
         |> Array.to_list
         |> List.map ~f:(Filename.concat f)
         |> List.append fs
         |> loop result
       | _ -> loop (f::result) fs)
    | []    -> result
  in loop [] [dir]
