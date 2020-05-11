open Core
open Cudd
open Wmc
open CoreGrammar
open Lexing
open Lexer
open Passes
open Parser


let rec parse_and_print print_parsed print_info lexbuf =
  let parsed = Util.parse_with_error lexbuf in
  if print_parsed then Format.printf "Parsed program: %s\n" (ExternalGrammar.string_of_prog parsed);
  let compiled = compile_program (from_external_prog parsed) in
  let zbdd = compiled.body.z in
  let z = Wmc.wmc zbdd compiled.ctx.weights in
  let table = VarState.get_table compiled.body.state in
  let probs = List.map table ~f:(fun (label, bdd) ->
      let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z in
      (label, prob)) in
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
    );
  if print_info then Man.print_info compiled.ctx.man;
  Format.printf "Final compiled size: %d\n"
    (VarState.state_size [compiled.body.state; VarState.Leaf(VarState.BddLeaf(compiled.body.z))]);
  Format.printf "Live: %d\n" (Man.get_node_count compiled.ctx.man)

let command =
  Command.basic
    ~summary:"Evaluate a dice program."
    ~readme:(fun () -> "")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map
       fname = anon ("filename" %: string)
     and print_info = flag "-show-info" no_arg ~doc:" print BDD info and statistics"
     and print_parsed = flag "-show-parsed" no_arg ~doc:" print parsed dice program"
     in fun () ->
       let inx = In_channel.create fname in
       let lexbuf = Lexing.from_channel inx in
       lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
       parse_and_print print_parsed print_info lexbuf
    )

let () =
  Command.run ~version:"1.0" command

