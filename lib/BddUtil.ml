open Core

type name_map = (Bdd.label, String.t) Hashtbl.Poly.t

(** prints a dotfile to the console *)
let dump_dot mgr (m: name_map) (b:Bdd.bddptr) =
  (** returns string corresponding to label at root of bdd *)
  let rec dump_dot_h (m: name_map) (b:Bdd.bddptr) seen =
    match Hashtbl.Poly.find seen b with
    | Some(v) -> v
    | None when Bdd.bdd_is_true mgr b ->
      Format.printf "T [shape=box, label=T]\n";
      Hashtbl.Poly.add_exn seen ~key:b ~data:"T";
      "T"
    | None when Bdd.bdd_is_false mgr b ->
      Format.printf "F [shape=box, label=F]\n";
      Hashtbl.Poly.add_exn seen ~key:b ~data:"F";
      "F"
    | None ->
      (* variable node*)
      let idx = Bdd.bdd_topvar mgr b in
      let name = Format.sprintf "idx%d_%d" (Bdd.int_of_label (Bdd.bdd_topvar mgr b)) (Hashtbl.hash b) in
      let lbl = match Hashtbl.Poly.find m idx with
        | Some(v) -> v
        | None -> name in
      Hashtbl.Poly.add_exn seen ~key:b ~data:name;
      (* print node *)
      Format.printf "%s [label = \"%s\" ]\n" name lbl;
      let (thn, els) = (Bdd.bdd_high mgr b, Bdd.bdd_low mgr b) in
      let s_thn = dump_dot_h m thn seen in
      let s_els = dump_dot_h m els seen in
      (* print edges *)
      Format.printf "%s -> %s\n%s -> %s [style=dashed]\n" name s_thn name s_els;
      name in
  Format.printf "digraph D {\n";
  let _ : String.t = dump_dot_h m b (Hashtbl.Poly.create ()) in
  Format.printf "}"



(** prints a dotfile to the console *)
let dump_dot_multiroot mgr (m: name_map) (b: Bdd.bddptr VarState.btree) : String.t =
  (** returns string corresponding to label at root of bdd *)
  let rec dump_dot_h s (m: name_map) (b:Bdd.bddptr) seen : (String.t * String.t) =
    match Hashtbl.Poly.find seen b with
    | Some(v) -> (s, v)
    | None when Bdd.bdd_is_true mgr b ->
      Hashtbl.Poly.add_exn seen ~key:b ~data:"T";
      (Format.sprintf "%s T [shape=box, label=T]\n" s, "T")
    | None when Bdd.bdd_is_false mgr b ->
      Hashtbl.Poly.add_exn seen ~key:b ~data:"F";
      (Format.sprintf "%s F [shape=box, label=F]\n" s, "F")
    | None ->
      (* variable node*)
      let idx = Bdd.bdd_topvar mgr b in
      let name = Format.sprintf "idx%d_%d" (Bdd.int_of_label (Bdd.bdd_topvar mgr b)) (Hashtbl.hash b) in
      let lbl = match Hashtbl.Poly.find m idx with
        | Some(v) -> v
        | None -> name in
      Hashtbl.Poly.add_exn seen ~key:b ~data:name;
      (* print node *)
      let (thn, els) = (Bdd.bdd_low mgr b, Bdd.bdd_high mgr b) in
      let (s1, s_thn) = dump_dot_h s m thn seen in
      let (s2, s_els) = dump_dot_h s1 m els seen in
      let r = (Format.sprintf "%s%s [label = \"%s\" ]\n%s -> %s\n%s -> %s [style=dashed]\n" s2 name lbl name s_thn name s_els, name) in
      r in
  let tbl = Hashtbl.Poly.create () in
  let rec print_h s curlbl (b: Bdd.bddptr VarState.btree) =
    match b with
    | Leaf(l) ->
      let (res, lbl) = dump_dot_h s m l tbl in
      let curlbl = if String.equal curlbl "" then "root" else curlbl in
      Format.sprintf "%s %s [shape = box]\n%s -> %s\n" res curlbl curlbl lbl
    | Node(l, r) ->
      let l_s = print_h s (Format.sprintf "%sl" curlbl) l in
      print_h l_s (Format.sprintf "%sr" curlbl) r
  in
  Format.sprintf "digraph D { %s } " (print_h "" "" b)
