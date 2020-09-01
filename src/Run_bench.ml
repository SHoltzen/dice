(* Documentation on the benchmark module:
   https://ocaml.janestreet.com/ocaml-core/latest/doc/core_bench/Core_bench/Bench/index.html *)
open Core
open Core_bench
open Util
open Lexing
open Lexer

let bench_prog (p: CoreGrammar.program) =
  let n = 5 in
  let i = (List.init n ~f:(fun i -> i)) in
  let l = List.map i ~f:(fun i ->
    let t0 = Unix.gettimeofday () in
    let _res = CoreGrammar.compile_program p in
    let t1 = Unix.gettimeofday () in
    (t1 -. t0)) in
  let fn = float_of_int n in
  let mean =  (List.fold l ~init:0.0 ~f:(+.)) /. fn in
  let stddev = Float.sqrt ((List.fold l ~init:0.0 ~f:(fun acc i -> acc +. Float.square (i -. mean))) /. fn) in
  (mean, stddev)


let run_benches () =
  let benches = dir_contents "benchmarks"
                |> List.filter ~f:(String.is_suffix ~suffix:".dice")
                |> List.map ~f:(fun filename -> (filename, In_channel.read_all filename)) in
  print_endline (Format.sprintf "Benchmark\tTime (s)\tStddev (s)");
  List.iter benches ~f:(fun (name, bench) ->
      let buf = Lexing.from_string bench in
      let parsed = try Parser.program Lexer.token buf with
        | SyntaxError msg ->
          fprintf stderr "%a: %s\n" print_position buf msg;
          failwith (Format.sprintf "Error parsing %s" bench)
        | Parser.Error ->
          fprintf stderr "%a: syntax error\n" print_position buf;
          failwith (Format.sprintf "Error parsing %s" bench) in

      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog parsed) in
      print_endline (Format.sprintf "%s\t%f\t%f" name t stddev)
    )

let gen_caesar (str: int list) =
  let prog = ref "
fun drawChar(key: int(26), observation: int(26)) {
    let drawnChar = discrete(0.08167, 0.01492, 0.02782, 0.04253, 0.12702, 0.02228, 0.02015, 0.06094, 0.06966, 0.0153, 0.0772, 0.04025, 0.02406, 0.06749, 0.07507, 0.01929, 0.00095, 0.05987, 0.06327, 0.09056, 0.02758, 0.00978, 0.02360, 0.00150, 0.01974, 0.00074) in
    let encrypted = key + drawnChar  in
    observe observation == encrypted
}
let key1  = discrete(0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538) in
" in
  List.iter str ~f:(fun c ->
      let new_ln = Format.sprintf "let a = drawChar(key1, int(26, %d)) in" c in
      prog := Format.sprintf "%s\n%s" !prog new_ln;
    );
  prog := Format.sprintf "%s\n%s" !prog "key1";
  parse_with_error (Lexing.from_string !prog)


(** [bench_caesar] runs the Caesar cipher scaling benchmarks.
    [inline_functions] is true if functions are inlined, false otherwise *)
let bench_caesar inline_functions =
  Format.printf "Length\tTime (s)\tStddev\n";
  let lst = [1; 100; 250; 500; 1000; 2500; 5000; 10000] in
  List.iter lst ~f:(fun len ->
      let caesar = gen_caesar (List.init len ~f:(fun i -> Random.int_incl 0 25)) in
      let inlined = (if inline_functions then Passes.inline_functions caesar else caesar) in
      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog inlined) in
      Format.printf "%d\t%f\t%f\n" len t stddev
    )


let gen_caesar_error (str: int list) =
  let prog = ref "
fun drawChar(key: int(26), observation: int(26)) {
    let drawnChar = discrete(0.08167, 0.01492, 0.02782, 0.04253, 0.12702, 0.02228, 0.02015, 0.06094, 0.06966, 0.0153, 0.0772, 0.04025, 0.02406, 0.06749, 0.07507, 0.01929, 0.00095, 0.05987, 0.06327, 0.09056, 0.02758, 0.00978, 0.02360, 0.00150, 0.01974, 0.00074) in
    let encrypted = key + drawnChar  in
    let fail = flip 0.0001 in
    if fail then (observe observation == drawnChar)
    else (observe observation == encrypted)
}
let key1  = discrete(0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538,0.038461538) in
" in
  List.iter str ~f:(fun c ->
      let new_ln = Format.sprintf "let a = drawChar(key1, int(26, %d)) in" c in
      prog := Format.sprintf "%s\n%s" !prog new_ln;
    );
  prog := Format.sprintf "%s\n%s" !prog "key1";
  parse_with_error (Lexing.from_string !prog)

(** [bench_caesar_error] runs the Caesar cipher scaling benchmarks with errors
    in the encryption. [inline_functions] is true if functions are inlined,
    false otherwise *)
let bench_caesar_error inline_functions =
  Format.printf "Length\tTime (s)\tStddev\n";
  let lst = [1; 100; 250; 500; 1000; 2500; 5000; 10000] in
  List.iter lst ~f:(fun len ->
      let caesar = gen_caesar_error (List.init len ~f:(fun i -> Random.int_incl 0 25)) in
      let inlined = (if inline_functions then Passes.inline_functions caesar else caesar) in
      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog inlined) in
      Format.printf "%d\t%f\t%f\n" len t stddev
    )


let gen_diamond n =
  let prog = ref "
fun diamond(s1: bool) {
//      if flip(0.5) then s1 else (flip(0.0001) && s1)
      let route = flip 0.5 in
      let s2 = if route then s1 else false in
      let s3 = if route then false else s1 in
      let drop = flip 0.0001 in
      s2 || (s3 && !drop)
}
" in
  let ln = ref "let s = true in" in
  for x = 1 to n do
      ln := Format.sprintf "%s\nlet s = diamond(s) in" !ln;
    done;
  prog := Format.sprintf "%s%s\ns" !prog !ln;
  parse_with_error (Lexing.from_string !prog)

let bench_diamond inline_functions =
  Format.printf "Length\tTime (s)\tStddev\n";
  let lst = [1; 100; 200; 300; 400; 500; 700; 800; 900; 1000; 2000; 3000; 4000; 5000] in
  List.iter lst ~f:(fun len ->
      let caesar = gen_diamond len in
      let inlined = (if inline_functions then Passes.inline_functions caesar else caesar) in
      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog inlined) in
      flush_all ();
      Format.printf "%d\t%f\t%f\n" len t stddev
    )


let gen_ladder n =
  let prog = ref "
fun ladder(s1: bool, s2: bool) {
      if s1 then
        if flip 0.001 then
          (false, false)
        else
           let f = flip 0.5 in (f, !f)
      else if s2 then
           let f = flip 0.5 in (f, !f)
      else (false, false)
}
      let x = (true, false) in
" in
  for x = 1 to n do
      let new_ln = Format.sprintf "let x = ladder(fst x, snd x) in" in
      prog := Format.sprintf "%s\n%s" !prog new_ln;
  done;
prog := Format.sprintf "%s\n%s" !prog "x" ;
  parse_with_error (Lexing.from_string !prog)

let bench_ladder inline_functions =
  Format.printf "Length\tTime (s)\tStddev\n";
  let lst = [1; 100; 200; 300; 400; 500; 700; 800; 900; 1000; 2000; 3000; 4000; 5000] in
  List.iter lst ~f:(fun len ->
      let caesar = gen_ladder len in
      let inlined = (if inline_functions then Passes.inline_functions caesar else caesar) in
      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog inlined) in
      Format.printf "%d\t%f\t%f\n" len t stddev
    )


let gen_motiv n =
  let prog = ref "
fun motiv(x: bool) {
  if x then flip 0.2 else flip 0.3
}
      let x = flip 0.1 in
" in
  for x = 1 to n do
      let new_ln = Format.sprintf "let x = motiv(x) in" in
      prog := Format.sprintf "%s\n%s" !prog new_ln;
  done;
prog := Format.sprintf "%s\n%s" !prog "x" ;
  parse_with_error (Lexing.from_string !prog)

let bench_motiv inline_functions =
  Format.printf "Length\tTime (s)\tStddev\n";
  let lst = [1; 100; 200; 300; 400; 500; 700; 800; 900; 1000; 2000; 3000; 4000; 5000] in
  List.iter lst ~f:(fun len ->
      let caesar = gen_motiv len in
      let inlined = (if inline_functions then Passes.inline_functions caesar else caesar) in
      let (t, stddev) = bench_prog (CoreGrammar.from_external_prog inlined) in
      Format.printf "%d\t%f\t%f\n" len t stddev
    )



let command =
  Command.basic
    ~summary:"Generate an MD5 hash of the input data"
    ~readme:(fun () -> "More detailed information")
    (let open Command.Let_syntax in
     let open Command.Param in
     let%map caesar = flag "-caesar" no_arg ~doc:" run caesar cipher scaling"
     and caesar_error = flag "-caesar-error" no_arg ~doc:" run caesar cipher with errors scaling"
     and diamond = flag "-diamond" no_arg ~doc:" run diamond"
     and ladder = flag "-ladder" no_arg ~doc:" run ladder"
     and baselines = flag "-baselines" no_arg ~doc:" run the baseline experiments"
     and motiv = flag "-motivating" no_arg ~doc:" run the motivating example"
     in fun () ->
       if baselines then (
         Format.printf "****************************************[Baselines]****************************************\n";
         run_benches ());
       if caesar then (
         Format.printf "****************************************[Caesar No Inline]****************************************\n";
         bench_caesar false;
         Format.printf "****************************************[Caesar Inlined]****************************************\n";
         bench_caesar true);
       if caesar_error then (
         Format.printf "****************************************[Caesar Error No Inline]****************************************\n";
         bench_caesar_error false;
         Format.printf "****************************************[Caesar Error Inlined]****************************************\n";
         bench_caesar_error true);
       if diamond then (
         Format.printf "****************************************[Diamond Non-Inlined]****************************************\n";
         bench_diamond false;
         Format.printf "****************************************[Diamond Inlined]****************************************\n";
         bench_diamond true);
       if ladder then (
         Format.printf "****************************************[Ladder Inlined]****************************************\n";
         bench_ladder true;
         Format.printf "****************************************[Ladder Non-Inlined]****************************************\n";
         bench_ladder false);
       if motiv then (
         Format.printf "****************************************[Motivating]****************************************\n";
         bench_ladder true
       )
    )

let () =
  Command.run ~version:"1.0" command

