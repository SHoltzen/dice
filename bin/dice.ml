open DiceLib
open Core
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
    let cols = List.transpose_exn rows in
    let tabs = List.map cols ~f:(fun col ->
      let lengths = List.map col ~f:String.length in
      let max_length = match List.max_elt lengths ~compare:Int.compare with
      | None -> 0.
      | Some(x) -> Float.of_int x in
      let max_spaces = (Float.iround_up_exn (max_length/. 4.)) * 4 in
      let spaces = List.map lengths ~f:(fun x -> max_spaces - x) in
      let min_spaces = match List.min_elt spaces ~compare:Int.compare with
      | None -> 0 
      | Some(x) -> x in
      let min_tab = if min_spaces = 0 then 1 else 0 in
      let tabs = List.map spaces ~f:(fun space ->
        let space_f = Float.of_int space in
        let less_tab = if space = max_spaces - 1 then 1 else 0 in
        let n = (Float.iround_up_exn (space_f/. 4.)) + min_tab - less_tab in
        String.of_char_list (List.init n ~f:(fun _ -> '\t'))
      )
      in tabs) 
      |> List.transpose_exn 
    in

    List.iter (List.zip_exn rows tabs) ~f:(fun (row, tab) ->
        List.iter (List.zip_exn row tab) ~f:(fun (i, t) -> Format.printf "%s%s" i t);
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

let rec print_pretty e =
  match e with
  | `Int(v) -> string_of_int v
  | `True -> "true"
  | `False -> "false"
  | `Tup(l, r) -> Format.sprintf "(%s, %s)" (print_pretty l) (print_pretty r)
  | `List(values) ->
    let rec format_elems = function
    | [] -> ""
    | [v] -> print_pretty v
    | v::vs -> print_pretty v ^ ", " ^ format_elems vs in
    "[" ^ format_elems values ^ "]"

let parse_and_print ~print_parsed ~print_internal ~print_size ~skip_table
    ~inline_functions ~sample_amount ~show_recursive_calls
    ~local_hoisting ~global_hoisting ~branch_elimination ~determinism ~sbk_encoding ~print_state_bdd
    ~show_function_size ~show_flip_count ~show_params ~print_unparsed ~print_lf ~print_cnf ~print_function_bdd
    ~recursion_limit ~max_list_length ~eager_eval ~no_compile ~max_flips ~float_wmc ~logical_formula
    ~cnf ~sharpsat_dir ~print_cnf_decisions ~verbose ~partial_marginals ~random_marginal ~show_lf_size
    lexbuf : result List.t = try
  let parsed = Compiler.parse_with_error lexbuf in
  let res = if print_parsed then [StringRes("Parsed program", (ExternalGrammar.string_of_prog parsed))] else [] in
  let parsed_norec = Passes.expand_recursion ?recursion_limit parsed in
  let cfg =
    { max_list_length = Option.value (Option.first_some max_list_length recursion_limit)
        ~default:Passes.default_config.max_list_length } in
  let parsed_marginals = match partial_marginals with
  | None -> Passes.select_marginals random_marginal parsed_norec
  | Some(x) -> Passes.select_marginals ~partial:x random_marginal parsed_norec in
  let optimize = local_hoisting || global_hoisting || branch_elimination || determinism in
  let (t, internal) =
    if inline_functions && optimize then
      (from_external_prog_optimize ~cfg sbk_encoding (Passes.inline_functions parsed_marginals) local_hoisting global_hoisting max_flips branch_elimination determinism)
    else if inline_functions && not optimize then
      (from_external_prog ~cfg sbk_encoding (Passes.inline_functions parsed_marginals))
    else if not inline_functions && optimize then
      (from_external_prog_optimize ~cfg sbk_encoding parsed_marginals local_hoisting global_hoisting max_flips branch_elimination determinism)
    else from_external_prog ~cfg sbk_encoding parsed_marginals in
  let res = if print_internal then res @ [StringRes("Parsed program", CoreGrammar.string_of_prog internal)] else res in
  let res = if print_unparsed then res @ [StringRes("Parsed program", CoreGrammar.string_of_prog_unparsed internal)] else res in
  let res = if show_flip_count then res @ [StringRes("Number of flips", CoreGrammar.count_flips internal)] else res in
  let res = if show_params then
    let distinct, total = ExternalGrammar.count_params parsed in
     res @ [StringRes("Number of Distinct Parameters", distinct); StringRes("Number of Parameters", total)] else res in
  let res = if print_lf || show_lf_size then 
    let log_form = from_core_prog internal in
    let res = if print_lf then
      res @ [StringRes("Logical formula", LogicalFormula.string_of_prog log_form)] else res in
    let res = if show_lf_size then
      res @ [StringRes("Logical formula size", string_of_int (LogicalFormula.size_of_lf log_form))] else res in
    res
    else res in
  if no_compile then res else match sample_amount with
  | None ->
    if cnf then 
      let log_form = from_core_prog internal in
      let wcnf = Compiler.compile_to_cnf log_form t in
      let res = if print_cnf then res @ [StringRes("CNF", LogicalFormula.string_of_wcnf wcnf)] else res in
      let s_dir = match sharpsat_dir with None -> "../sharpsat-td/bin/" | Some(d) -> d in
      
      let probs = List.map wcnf.table ~f:(fun (label, cnf_expr) -> 
        let prob, decisions = Compiler.compute_cnf ~debug:verbose s_dir cnf_expr wcnf.weights in
        if Bignum.(prob = zero) then (label, Bignum.zero, decisions) else
          (label, prob, decisions))
      in
      let res = if print_cnf_decisions then 
        let avg = List.fold probs ~init:Bignum.zero ~f:(fun acc (_, _, dec) -> Bignum.(acc + dec)) in
        let x = Bignum.of_int(List.length probs) in
        let avg = Bignum.(avg / x) in
        res @ [StringRes("Average CNF decisions", Bignum.to_string_hum avg)] else res in
      let res = if skip_table then res else res @
        (let table = if print_cnf_decisions then
            [["Value"; "Probability"; "Decisions"]] @ List.map probs ~f:(fun (label, prob, dec) ->
              [print_pretty label; Bignum.to_string_hum prob; Bignum.to_string_hum dec])
          else
            [["Value"; "Probability"]] @ List.map probs ~f:(fun (label, prob, _) ->
              [print_pretty label; Bignum.to_string_hum prob])
        in
        [TableRes("CNF Joint Distribution", table)])
      in
      res
    else
      let compiled = if logical_formula then 
        let log_form = from_core_prog internal in
        Compiler.compile_to_bdd log_form else Compiler.compile_program internal ~eager_eval in
      let zbdd = compiled.body.z in
      let res = if skip_table then res else res @
        (let z = Wmc.wmc ~float_wmc compiled.ctx.man zbdd compiled.ctx.weights in
        let table = VarState.get_table cfg compiled.ctx.man compiled.body.state t in
        let probs = List.map table ~f:(fun (label, bdd) ->
            if Bignum.(z = zero) then (label, Bignum.zero) else
              let prob = Bignum.((Wmc.wmc ~float_wmc compiled.ctx.man (Bdd.bdd_and compiled.ctx.man bdd zbdd) compiled.ctx.weights) / z) in
              (label, prob)) in
        let l = [["Value"; "Probability"]] @
          List.map probs ~f:(fun (typ, prob) -> [print_pretty typ; Bignum.to_string_hum prob]) in
        [TableRes("Joint Distribution", l)]
        ) in
      (* let res = if show_recursive_calls then res @ [StringRes("Number of recursive calls",
      *                                                         Format.sprintf "%f" (Man.num_recursive_calls compiled.ctx.man))]
      *   else res in *)
      (* let res = if show_function_size then
      *     let all_sizes = List.map (Hashtbl.to_alist compiled.ctx.funcs) ~f:(fun (key, data) ->
      *         (\* let sz = VarState.state_size [data.body.state; VarState.Leaf(data.body.z)] in *\)
      *         let sz = Bdd.size (VarState.extract_leaf data.body.state) in
      *         StringRes(Format.sprintf "Size of function '%s'" key, string_of_int sz)
      *       ) in
      *     res @ all_sizes else res in
      * let res = if print_function_bdd then
      *     let all_bdds = List.map (Hashtbl.to_alist compiled.ctx.funcs) ~f:(fun (key, data) ->
      *         let bdd = BddUtil.dump_dot_multiroot compiled.ctx.name_map data.body.state in
      *         StringRes(Format.sprintf "BDD for function '%s'" key, bdd)
      *       ) in
      *     res @ all_bdds else res in *)
      let res = if print_size then
          res @ [StringRes("Final compiled BDD size",
                          string_of_int (VarState.state_size compiled.ctx.man [compiled.body.state; VarState.Leaf(compiled.body.z)]))] 
        else res in
      let res = if print_state_bdd then
          res @ [StringRes("State BDD (graphviz format)",
                          BddUtil.dump_dot_multiroot compiled.ctx.man compiled.ctx.name_map compiled.body.state);
                StringRes("State accepting BDD (graphviz format)",
                          BddUtil.dump_dot_multiroot compiled.ctx.man compiled.ctx.name_map (VarState.Leaf(compiled.body.z)))
                ]
        else res in
      Bdd.man_print_stats compiled.ctx.man;
      res
  (* | Some(n) ->
   *   let sz = ref 0 in
   *   let rec draw_sample (prob, oldz) n =
   *     if n = 0 then (prob, oldz)
   *     else
   *       let compiled = Compiler.compile_program ~eager_eval:true internal in
   *       sz := !sz + VarState.state_size [compiled.body.state; Leaf(compiled.body.z)];
   *       let table = VarState.get_table cfg compiled.body.state t in
   *       let zbdd = compiled.body.z in
   *       let z = Wmc.wmc zbdd compiled.ctx.weights in
   *       let probs = List.map table ~f:(fun (label, bdd) ->
   *           if Util.within_epsilon z 0.0 then (label, 0.0) else
   *             let prob = (Wmc.wmc (Bdd.dand bdd zbdd) compiled.ctx.weights) in
   *             (label, prob)) in
   *       (match prob with
   *        | None -> draw_sample (Some(probs), z) (n-1)
   *        | Some(v) ->
   *          let summed = List.map (List.zip_exn v probs) ~f:(fun ((_, a), (lbl, b)) -> (lbl, a +. b)) in
   *          draw_sample (Some(summed), z +. oldz) (n-1)) in
   *   let (res_state, z) = draw_sample (None, 0.0) n in
   *   let res = if skip_table then [] else
   *       let l = [["Value"; "Probability"]] @
   *         List.map (Option.value_exn res_state) ~f:(fun (typ, prob) ->
   *           [print_pretty typ; string_of_float (prob /. z)]) in
   *       [TableRes("Joint Probability", l)] in
   *   let res = if print_size then
   *       res @ [StringRes("Compiled BDD size", string_of_float(float_of_int !sz /. float_of_int n))] else res in
   *   res *)
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
     and local_hoisting = flag "-local-hoisting" no_arg ~doc:" optimize dice program before compilation using local flip-hoisting"
     and global_hoisting = flag "-global-hoisting" no_arg ~doc: " perform global flip-hoisting."
     and branch_elimination = flag "-branch-elimination" no_arg ~doc:" optimize dice program before compilation using branch elimination"
     and determinism = flag "-determinism" no_arg ~doc:" optimize dice program before compilation using determinism"
     and sbk_encoding = flag "-sbk-encoding" no_arg ~doc:" use Sang-Beame-Kautz encoding for integers and categorical distributions"
     and show_function_size = flag "-show-function-size" no_arg ~doc:" print size of all function BDDs"
     and inline_functions = flag "-inline-functions" no_arg ~doc:" inline all function calls"
     and print_internal = flag "-show-internal" no_arg ~doc:" print desugared dice program"
     and print_state_bdd = flag "-print-state-bdd" no_arg ~doc:" print final compiled state BDD (in graphviz format)"
     and print_function_bdd = flag "-print-function-bdd" no_arg ~doc:" print final compiled function state BDD (in graphviz format)"
     and print_unparsed = flag "-show-unparsed" no_arg ~doc:" print unparsed desugared dice program"
     and print_lf = flag "-show-logical-formula" no_arg ~doc:" print logical formula of dice program"
     and print_cnf = flag "-show-cnf" no_arg ~doc:" print CNF of dice program"
     and skip_table = flag "-skip-table" no_arg ~doc:" skip printing the joint probability distribution"
     and show_recursive_calls = flag "-num-recursive-calls" no_arg ~doc:" show the number of recursive calls invoked during compilation"
     and eager_eval = flag "-eager-eval" no_arg ~doc:" eager let compilation"
     and recursion_limit = flag "-recursion-limit" (optional int) ~doc:" maximum recursion depth"
     and max_list_length = flag "-max-list-length" (optional int) ~doc:" maximum list length"
     and show_flip_count = flag "-show-flip-count" no_arg ~doc:" show the number of flips in the program"
     and show_params = flag "-show-params" no_arg ~doc:" show the sum of number of unique parameters in each table in the program"
     and no_compile = flag "-no-compile" no_arg ~doc: " parse the program only"
     and max_flips = flag "-max-flips" (optional int) ~doc: " limit the number of flips during flip-hoisting"
     and float_wmc = flag "-float-wmc" no_arg ~doc:" use float-based wmc"
     and logical_formula = flag "-logical-formula" no_arg ~doc:" use logical formula interface"
     and cnf = flag "-cnf" no_arg ~doc:" compiles to CNF"
     and print_cnf_decisions = flag "-show-cnf-decisions" no_arg ~doc:" show the number of decisions performed by SharpSAT-td"
     (* and print_marginals = flag "-show-marginals" no_arg ~doc:" print the marginal probabilities of a tuple in depth-first order" *)
     and json = flag "-json" no_arg ~doc:" print output as JSON"
     and sharpsat_dir = flag "-sharpsat-dir" (optional string) ~doc:" path to sharpsat binary (default ../sharpsat-td/bin/)"
     and verbose = flag "-verbose" no_arg ~doc:" print additional debugging output"
     and partial_marginals = flag "-partial-marginals" (optional int) ~doc:" computes a random subset of the marginals of size n"
     and random_marginal = flag "-random-marginal" no_arg ~doc:" computes the results of a random marginal. Takes precedence over partial marginals"
     and show_lf_size = flag "-show-lf-size" no_arg ~doc:" show the number of nodes in the logical formula"
     in fun () ->
       let inx = In_channel.create fname in
       let lexbuf = Lexing.from_channel inx in
       lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
       let r = (parse_and_print ~print_parsed ~print_internal ~sample_amount
                  ~print_size ~inline_functions ~skip_table ~local_hoisting ~global_hoisting
                  ~branch_elimination ~determinism ~sbk_encoding ~show_recursive_calls ~print_state_bdd
                  ~show_function_size ~show_flip_count ~show_params ~print_unparsed ~print_lf ~print_cnf ~print_function_bdd
                  ~recursion_limit ~max_list_length ~eager_eval ~no_compile ~max_flips ~float_wmc ~logical_formula
                  ~cnf ~sharpsat_dir ~print_cnf_decisions ~verbose ~partial_marginals ~random_marginal ~show_lf_size
                  lexbuf) in
       if json then Format.printf "%s" (Yojson.to_string (`List(List.map r ~f:json_res)))
       else List.iter r ~f:print_res
    )

let () =
  Command.run ~version:"1.0" command


