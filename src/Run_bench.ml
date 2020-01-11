(* Documentation on the benchmark module:
   https://ocaml.janestreet.com/ocaml-core/latest/doc/core_bench/Core_bench/Bench/index.html *)
open Core
open Core_bench.Std
open CoreGrammar
open Wmc
open BddUtil
open Util
open Lexing
open Lexer


let () =
  Random.self_init ();
  let benches = dir_contents "benchmarks"
                |> List.filter ~f:(String.is_suffix ~suffix:".dice")
                |> List.map ~f:(fun filename -> Bench.Test.create ~name:filename (fun () ->
                    let contents = In_channel.read_all filename in
                    let buf = Lexing.from_string contents in
                    let parsed = try Parser.program Lexer.token buf with
                      | SyntaxError msg ->
                        fprintf stderr "%a: %s\n" print_position buf msg;
                        failwith (Format.sprintf "Error parsing %s" contents)
                      | Parser.Error ->
                        fprintf stderr "%a: syntax error\n" print_position buf;
                        failwith (Format.sprintf "Error parsing %s" contents) in
                    compile_program (from_external_prog parsed)
                  )) in
  Command.run (Bench.make_command benches)

