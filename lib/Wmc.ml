open Core
open Bdd

(** map from variable index to (low weight, high weight) *)
type weight = (label, (float*float)) Hashtbl.Poly.t

(** Perform a weighted model count of the BDD `bdd` with weight function `w` *)
let wmc mgr (bdd : bddptr) (w: weight) =
  (* internal memoized recursive weighted model count *)
  let rec wmc_rec bdd w cache : float=
    if bdd_is_true mgr bdd then 1.0
    else if bdd_is_false mgr bdd then 0.0
    else match Hashtbl.Poly.find cache bdd with
      | Some v -> v
      | _ ->
        (* compute weight of children *)
        let (thn, els) = (bdd_high mgr bdd, bdd_low mgr bdd) in
        let thnw = wmc_rec thn w cache and
          elsw = wmc_rec els w cache in
        (* compute new weight, add to cache *)
        let (loww, highw) = try Hashtbl.Poly.find_exn w (bdd_topvar mgr bdd)
          with _ -> failwith (Format.sprintf "Could not find variable %d" (Bdd.int_of_label (bdd_topvar mgr bdd)))in
        let new_weight = (highw *. thnw) +. (loww *. elsw) in
        Hashtbl.Poly.add_exn cache ~key:bdd ~data:new_weight;
        new_weight in
  wmc_rec bdd w (Hashtbl.Poly.create ())
