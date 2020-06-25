open DiceLib
open Core
open Cudd
open Passes


let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)


let parse_and_print ~print_parsed ~print_info ~print_internal
    ~print_size ~skip_table ~print_marginals ~inline_functions
    ~sample_amount lexbuf = try
  let parsed = Compiler.parse_with_error lexbuf in
  if print_parsed then Format.printf "==========Parsed program==========\n%s\n" (ExternalGrammar.string_of_prog parsed);
  let (t, internal) = if inline_functions then
      (from_external_prog (Passes.inline_functions parsed))
    else from_external_prog parsed in
  if print_internal then Format.printf "==========Desugared program==========\n%s\n" (CoreGrammar.string_of_prog internal);
  match sample_amount with
  | None ->
    let compiled = Compiler.compile_program internal in
    let zbdd = compiled.body.z in
    let z = Wmc.wmc zbdd compiled.ctx.weights in
    if not skip_table then
      (let table = VarState.get_table compiled.body.state t in
       let probs = List.map table ~f:(fun (label, bdd) ->
           if Util.within_epsilon z 0.0 then (label, 0.0) else
             let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z in
             (label, prob)) in
       Format.printf "==========Joint Distribution==========\n";
       Format.printf "Value\tProbability\n";
       List.iter probs ~f:(fun (typ, prob) ->
           let rec print_pretty e =
             match e with
             | `Int(v) -> string_of_int v
             | `True -> "true"
             | `False -> "false"
             | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
             | _ -> failwith "ouch" in
           Format.printf "%s\t%f\n" (print_pretty typ) prob;
         ));
    if print_marginals then
      (Format.printf "==========Marginal Probabilities==========\n";
       VarState.iter_tree compiled.body.state (fun bdd ->
           Format.printf "Value\tProbability\n";
           Format.printf "true\t%f\n" ((Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z);
           Format.printf "false\t%f\n" ((Wmc.wmc (Bdd.dand (Bdd.dnot bdd) zbdd) compiled.ctx.weights) /. z);
           Format.printf "\n";
         ));
    if print_info then (Format.printf "==========BDD Manager Info==========\n"; Man.print_info compiled.ctx.man);
    if print_size then (Format.printf "==========Final compiled BDD size:==========\n%d\n"
                          (VarState.state_size [compiled.body.state; VarState.Leaf(compiled.body.z)]))
  | Some(n) ->
    let rec draw_sample (prob, oldz) n =
      if n = 0 then (prob, oldz)
      else
        let compiled = Compiler.compile_program internal in
        let table = VarState.get_table compiled.body.state t in
        let zbdd = compiled.body.z in
        let z = Wmc.wmc zbdd compiled.ctx.weights in
        let probs = List.map table ~f:(fun (label, bdd) ->
            if Util.within_epsilon z 0.0 then (label, 0.0) else
              let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) in
              (label, prob)) in
        (match prob with
         | None -> draw_sample (Some(probs), z) (n-1)
         | Some(v) ->
           let summed = List.map (List.zip_exn v probs) ~f:(fun ((_, a), (lbl, b)) -> (lbl, a +. b)) in
           draw_sample (Some(summed), z +. oldz) (n-1)) in
    let (res_state, z) = draw_sample (None, 0.0) n in
    Format.printf "==========Joint Distribution==========\n";
    Format.printf "Value\tProbability\n";
    List.iter (Option.value_exn res_state) ~f:(fun (typ, prob) ->
        let rec print_pretty e =
          match e with
          | `Int(v) -> string_of_int v
          | `True -> "true"
          | `False -> "false"
          | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
          | _ -> failwith "ouch" in
        Format.printf "%s\t%f\n" (print_pretty typ) (prob /. z);
      )
  with Compiler.Syntax_error(s) -> Format.printf "Syntax error: %s" s


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
     and sample_amount = flag "-sample" (optional int) ~doc:" number of samples to draw"
     and print_parsed = flag "-show-parsed" no_arg ~doc:" print parsed dice program"
     and inline_functions = flag "-inline-functions" no_arg ~doc:" inline all function calls"
     and print_internal = flag "-show-internal" no_arg ~doc:" print desugared dice program"
     and skip_table = flag "-skip-table" no_arg ~doc:" skip printing the joint probability distribution"
     and print_marginals = flag "-show-marginals" no_arg ~doc:" print the marginal probabilities of a tuple in depth-first order"
     in fun () ->
       let inx = In_channel.create fname in
       let lexbuf = Lexing.from_channel inx in
       lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
       parse_and_print ~print_parsed ~print_info ~print_internal ~sample_amount
         ~print_size ~inline_functions ~skip_table ~print_marginals lexbuf
    )

let () =
  Command.run ~version:"1.0" command


