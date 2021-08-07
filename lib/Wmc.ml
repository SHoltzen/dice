open Core
open Cudd
open Bignum

(** map from variable index to (low weight, high weight) *)
type weight = (int, (Bignum.t * Bignum.t)) Hashtbl.Poly.t


let hashtable_to_float (low, high) = 
  (Bignum.to_float low, Bignum.to_float high) 

(** Perform a weighted model count of the BDD `bdd` with weight function `w` *)
let wmc ~float_wmc bdd (w: weight) =
  (* internal memoized recursive weighted model count *)
  let rec wmc_rec bdd w cache addop multop one zero =
    if Bdd.is_true bdd then one
    else if Bdd.is_false bdd then zero
    else match Hashtbl.Poly.find cache bdd with
      | Some v -> v
      | _ ->
        (* compute weight of children *)
        let (thn, els) = (Bdd.dthen bdd, Bdd.delse bdd) in
        let thnw = wmc_rec thn w cache addop multop one zero and
          elsw = wmc_rec els w cache addop multop one zero in
        (* compute new weight, add to cache *)
        let (loww, highw) = try Hashtbl.Poly.find_exn w (Bdd.topvar bdd)
          with _ -> failwith (Format.sprintf "Could not find variable %d" (Bdd.topvar bdd))in
        let new_weight = (addop (multop highw thnw) (multop loww elsw)) in
        Hashtbl.Poly.add_exn cache ~key:bdd ~data:new_weight;
        new_weight in
  if float_wmc then Bignum.of_float_dyadic 
          (wmc_rec bdd (Hashtbl.Poly.map w hashtable_to_float) (Hashtbl.Poly.create ()) (+.) ( *. ) 1. 0.) 
    else wmc_rec bdd w (Hashtbl.Poly.create ()) Bignum.(+) Bignum.( * ) Bignum.one Bignum.zero
