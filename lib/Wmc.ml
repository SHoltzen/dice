open Core
open Cudd

(** map from variable index to (low weight, high weight) *)
type weight = (int, (float*float)) Hashtbl.Poly.t

(** Perform a weighted model count of the BDD `bdd` with weight function `w` *)
let wmc bdd (w: weight) =
  (* internal memoized recursive weighted model count *)
  let rec wmc_rec bdd w cache : float=
    if Bdd.is_true bdd then 1.0
    else if Bdd.is_false bdd then 0.0
    else match Hashtbl.Poly.find cache bdd with
      | Some v -> v
      | _ ->
        (* compute weight of children *)
        let (thn, els) = (Bdd.dthen bdd, Bdd.delse bdd) in
        let thnw = wmc_rec thn w cache and
          elsw = wmc_rec els w cache in
        (* compute new weight, add to cache *)
        let (loww, highw) = try Hashtbl.Poly.find_exn w (Bdd.topvar bdd)
          with _ -> failwith (Format.sprintf "Could not find variable %d" (Bdd.topvar bdd))in
        let new_weight = (highw *. thnw) +. (loww *. elsw) in
        Hashtbl.Poly.add_exn cache bdd new_weight;
        new_weight in
  wmc_rec bdd w (Hashtbl.Poly.create ())
