open DiceLib
open Core
open Cudd
open Passes


(** List of rows in a table *)
type tableres = String.t List.t List.t

type result =
    TableRes of String.t * tableres
  | StringRes of String.t * String.t
  | ErrorRes of String.t

let print_res r =
  match r with
  | TableRes(name, rows) ->
    Format.printf "================[ %s ]================\n" name;
    List.iter rows ~f:(fun row ->
        List.iter row ~f:(fun i -> Format.printf "%s\t" i);
        Format.printf "\n";
      );
    Format.printf "\n"
  | StringRes(name, value) ->
    Format.printf "================[ %s ]================\n" name;
    Format.printf "%s\n" value;
  | ErrorRes(value) ->
    Format.printf "================[ Error ]================\n";
    Format.printf "%s\n" value

let json_res r : Yojson.json =
  let open Yojson in
  match r with
  | StringRes(name, v) -> `Assoc([name, `String(v)])
  | ErrorRes(v) -> `Assoc(["error", `String(v)])
  | TableRes(name, rows) ->
    let tbljson = `List(List.map rows ~f:(fun row ->
      `List(List.map row ~f:(fun i -> `String(i))))) in
    `Assoc([name, tbljson])

let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let parse_and_print ~print_parsed ~print_internal ~print_size ~skip_table
    ~inline_functions ~sample_amount ~flip_lifting ~branch_elimination ~determinism lexbuf : result List.t = try
  let parsed = Compiler.parse_with_error lexbuf in
  let res = if print_parsed then [StringRes("Parsed program", (ExternalGrammar.string_of_prog parsed))] else [] in
  let optimize = flip_lifting or branch_elimination or determinism in
  let (t, internal) =
    if inline_functions && optimize then
      (from_external_prog_optimize (Passes.inline_functions parsed) flip_lifting branch_elimination determinism)
    else if inline_functions && not optimize then
      (from_external_prog (Passes.inline_functions parsed))
    else if not inline_functions && optimize then
      (from_external_prog_optimize parsed flip_lifting branch_elimination determinism)
    else from_external_prog parsed in
  let res = if print_internal then res @ [StringRes("Parsed program", CoreGrammar.string_of_prog internal)] else res in
  match sample_amount with
  | None ->
    let compiled = Compiler.compile_program internal in
    let zbdd = compiled.body.z in
    let z = Wmc.wmc zbdd compiled.ctx.weights in
    let res = if skip_table then res else res @
      (let table = VarState.get_table compiled.body.state t in
       let probs = List.map table ~f:(fun (label, bdd) ->
           if Util.within_epsilon z 0.0 then (label, 0.0) else
             let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) /. z in
             (label, prob)) in
       let l = [["Value"; "Probability"]] @ List.map probs ~f:(fun (typ, prob) ->
           let rec print_pretty e =
             match e with
             | `Int(v) -> string_of_int v
             | `True -> "true"
             | `False -> "false"
             | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
             | _ -> failwith "ouch" in
           [print_pretty typ; string_of_float prob]
         ) in
       [TableRes("Joint Distribution", l)]
      ) in
    (* if print_info then (Format.printf "==========BDD Manager Info==========\n"; Man.print_info compiled.ctx.man); *)
    let res = if print_size then
        res @ [StringRes("Final compiled BDD size",
                         string_of_int (VarState.state_size [compiled.body.state; VarState.Leaf(compiled.body.z)]))]
      else res in
    res
  | Some(n) ->
    let sz = ref 0 in
    let rec draw_sample (prob, oldz) n =
      if n = 0 then (prob, oldz)
      else
        let compiled = Compiler.compile_program internal in
        sz := !sz + VarState.state_size [compiled.body.state; Leaf(compiled.body.z)];
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
    let res = if skip_table then [] else
        let l = [["Value"; "Probability"]] @ List.map (Option.value_exn res_state) ~f:(fun (typ, prob) ->
            let rec print_pretty e =
              match e with
              | `Int(v) -> string_of_int v
              | `True -> "true"
              | `False -> "false"
              | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
              | _ -> failwith "ouch" in
            [print_pretty typ; string_of_float (prob /. z)]
          ) in
        [TableRes("Joint Probability", l)] in
    let res = if print_size then
        res @ [StringRes("Compiled BDD size", string_of_float(float_of_int !sz /. float_of_int n))] else res in
    res
  with Compiler.Syntax_error(s) -> [ErrorRes(s)]


let command =
  Command.basic
    ~summary:"Evaluate a dice program. By default, prints the joint probability of each returned variable in depth-first order."
    ~readme:(fun () -> "")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map
       fname = anon ("filename" %: string)
     (* and print_info = flag "-show-info" no_arg ~doc:" print BDD info and statistics" *)
     and print_size = flag "-show-size" no_arg ~doc:" show the size of the final compiled BDD"
     and sample_amount = flag "-sample" (optional int) ~doc:" number of samples to draw"
     and print_parsed = flag "-show-parsed" no_arg ~doc:" print parsed dice program"
     and flip_lifting = flag "-flip-lifting" no_arg ~doc:" optimize dice program before compilation using flip lifting"
     and branch_elimination = flag "-branch-elimination" no_arg ~doc:" optimize dice program before compilation using branch elimination"
     and determinism = flag "-determinism" no_arg ~doc:" optimize dice program before compilation using determinism"
     and inline_functions = flag "-inline-functions" no_arg ~doc:" inline all function calls"
     and print_internal = flag "-show-internal" no_arg ~doc:" print desugared dice program"
     and skip_table = flag "-skip-table" no_arg ~doc:" skip printing the joint probability distribution"
     (* and print_marginals = flag "-show-marginals" no_arg ~doc:" print the marginal probabilities of a tuple in depth-first order" *)
     and json = flag "-json" no_arg ~doc:" print output as JSON"
     in fun () ->
       let inx = In_channel.create fname in
       let lexbuf = Lexing.from_channel inx in
       lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
       let r = (parse_and_print ~print_parsed ~print_internal ~sample_amount
                  ~print_size ~inline_functions ~skip_table ~flip_lifting ~branch_elimination ~determinism lexbuf) in
       if json then Format.printf "%s" (Yojson.to_string (`List(List.map r ~f:json_res)))
       else List.iter r ~f:print_res
    )

let () =
  Command.run ~version:"1.0" command


