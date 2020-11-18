open Cudd
open Core

type name_map = (int, String.t) Hashtbl.Poly.t

(** prints a dotfile to the console *)
let dump_dot (m: name_map) (b:Bdd.dt) =
  (** returns string corresponding to label at root of bdd *)
  let rec dump_dot_h (m: name_map) (b:Bdd.dt) seen =
    match Hashtbl.Poly.find seen b with
    | Some(v) -> v
    | None when Bdd.is_true b ->
      Format.printf "T [shape=box, label=T]\n";
      Hashtbl.Poly.add_exn seen ~key:b ~data:"T";
      "T"
    | None when Bdd.is_false b ->
      Format.printf "F [shape=box, label=F]\n";
      Hashtbl.Poly.add_exn seen ~key:b ~data:"F";
      "F"
    | None ->
      (* variable node*)
      let idx = Bdd.topvar b in
      let name = Format.sprintf "idx%d_%d" (Bdd.topvar b) (Hashtbl.hash b) in
      let lbl = match Hashtbl.Poly.find m idx with
        | Some(v) -> v
        | None -> name in
      (* print node *)
      Format.printf "%s [label = \"%s\" ]\n" name lbl;
      let (thn, els) = (Bdd.dthen b, Bdd.delse b) in
      let s_thn = dump_dot_h m thn seen in
      let s_els = dump_dot_h m els seen in
      (* print edges *)
      Format.printf "%s -> %s\n%s -> %s [style=dashed]\n" name s_thn name s_els;
      name in
  Format.printf "digraph D {\n";
  let _ : String.t = dump_dot_h m b (Hashtbl.Poly.create ()) in
  Format.printf "}";
  Format.print_flush ()

