open Core
open Cudd
open Wmc
open CoreGrammar
open Lexing
open Lexer
open Passes
open Parser


let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let rec parse_and_print print_parsed print_info print_size skip_table print_marginals lexbuf = try
  let parsed = Util.parse_with_error lexbuf in
  if print_parsed then Format.printf "==========Parsed program==========\n%s\n" (ExternalGrammar.string_of_prog parsed);
  let compiled = compile_program (from_external_prog parsed) in
  let zbdd = compiled.body.z in
  let z = Wmc.wmc zbdd compiled.ctx.weights in
  if not skip_table then
  (let table = VarState.get_table compiled.body.state in
   let probs = List.map table ~f:(fun (label, bdd) ->
       let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z in
       (label, prob)) in
   Format.printf "==========Joint Distribution==========\n";
   Format.printf "Value\tProbability\n";
   List.iter probs ~f:(fun (typ, prob) ->
         let rec print_pretty e =
           match e with
           | `Int(sz, v) -> string_of_int v
           | `True -> "true"
           | `False -> "false"
           | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
           | _ -> failwith "ouch" in
         Format.printf "%s\t%f\n" (print_pretty typ) prob;
       ));
  if print_marginals then
    (Format.printf "==========Marginal Probabilities==========\n";
     VarState.iter_tree compiled.body.state (fun state ->
         match state with
         | BddLeaf(bdd) ->
           Format.printf "Value\tProbability\n";
           Format.printf "true\t%f\n" ((Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z);
           Format.printf "false\t%f\n" ((Wmc.wmc (Bdd.dand (Bdd.dnot bdd) zbdd) compiled.ctx.weights) /. z);
           Format.printf "\n";
         | IntLeaf(l) ->
           Format.printf "Value\tProbability\n";
           List.iteri l ~f:(fun idx bdd ->
               Format.printf "%d\t%f\n" idx ((Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z);
             );
           Format.printf "\n"
       ));
  if print_info then (Format.printf "==========BDD Manager Info=========="; Man.print_info compiled.ctx.man);
  if print_size then (Format.printf "==========Final compiled BDD size: %d\n=========="
                        (VarState.state_size [compiled.body.state; VarState.Leaf(VarState.BddLeaf(compiled.body.z))]))
  with Util.Syntax_error(s) -> Format.printf "Syntax error: %s" s


let command =
  Command.basic
    ~summary:"Evaluate a dice program. By default, prints the joint probability of each returned variable in depth-first order."
    ~readme:(fun () -> "")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map
       fname = anon ("filename" %: string)
     and print_info = flag "-show-info" no_arg ~doc:" print BDD info and statistics"
     and print_size = flag "-show-size" no_arg ~doc:" show the size of the final compiled BDD"
     and print_parsed = flag "-show-parsed" no_arg ~doc:" print parsed dice program"
     and skip_table = flag "-skip-table" no_arg ~doc:" skip printing the joint probability distribution"
     and print_marginals = flag "-show-marginals" no_arg ~doc:" print the marginal probabilities of a tuple in depth-first order"
     in fun () ->
       let inx = In_channel.create fname in
       let lexbuf = Lexing.from_channel inx in
       lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
       parse_and_print print_parsed print_info print_size skip_table print_marginals lexbuf
    )

let () =
  Command.run ~version:"1.0" command


