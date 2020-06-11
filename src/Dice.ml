open Core
open Cudd
open Wmc
open CoreGrammar
open Lexing
open Lexer
open Passes
open Parser
open Optimization
open BddUtil
open VarState

let rec parse_and_print lexbuf =
  let parsed = Util.parse_with_error lexbuf in
  let optimized = Optimization.optimize parsed in
  (* Format.printf "%s\n" (ExternalGrammar.string_of_eexpr optimized.body); *)
  let compiled = compile_program (CoreGrammar.from_external_prog optimized) in
  let zbdd = compiled.body.z in
  (* dump_dot compiled.ctx.name_map (extract_bdd compiled.body.state); *)
  let z = Wmc.wmc zbdd compiled.ctx.weights in
  let table = VarState.get_table compiled.body.state in
  let probs = List.map table ~f:(fun (label, bdd) ->
      let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z in
      (label, prob)) in
  (* Format.printf "Value\tProbability\n"; *)
  (* let rec top i lst acc =
    match lst with
    | [] -> List.rev acc
    | head::tail -> 
      if i = 0 then
        List.rev acc
      else
        top (i - 1) tail (head::acc)
  in
  let top_three = top 3 (List.sort (fun (l1, p1) (l2, p2) -> if p1 > p2 then -1 else if p1 < p2 then 1 else 0) probs) [] in *)
  (* List.iter probs ~f:(fun (typ, prob) ->
      let rec print_pretty e =
        match e with
        | `Int(sz, v) -> string_of_int v
        | `True -> "true"
        | `False -> "false"
        | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
        | _ -> failwith "ouch" in
      Format.printf "%s\t%f\n" (print_pretty typ) prob;
    ); *)
  Format.printf "Final compiled size: %d\n" (VarState.state_size [compiled.body.state])
  (* let prob = CoreGrammar.get_prob (CoreGrammar.from_external_prog parsed) in
   * Format.printf "prob: %f\n" prob *)

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

let () =
  Command.basic_spec ~summary:"Parse and compute prob"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command.run
