open Core
open Bdd

(** map from variable index to (low weight, high weight) *)
type weight = (label, (Bignum.t*Bignum.t)) Core.Hashtbl.Poly.t

let hashtable_to_float (low, high) = 
  (Bignum.to_float low, Bignum.to_float high) 

let hashtable_to_log (low, high) = 
  (LogProbability.make low, LogProbability.make high)





(** Perform a weighted model count of the BDD `bdd` with weight function `w` *)
let wmc ~wmc_type mgr (bdd : bddptr) (w: weight) =
  (* internal memoized recursive weighted model count *)
  let rec wmc_rec bdd w cache addop multop one zero =
    if bdd_is_true mgr bdd then one
    else if bdd_is_false mgr bdd then zero
    else match Hashtbl.Poly.find cache bdd with
      | Some v -> v
      | _ ->
        (* compute weight of children *)
        let (thn, els) = (bdd_high mgr bdd, bdd_low mgr bdd) in
        let thnw = wmc_rec thn w cache addop multop one zero and
          elsw = wmc_rec els w cache addop multop one zero in
        (* compute new weight, add to cache *)
        let (loww, highw) = try Hashtbl.Poly.find_exn w (bdd_topvar mgr bdd)
          with _ -> failwith (Format.sprintf "Could not find variable %d" (Bdd.int_of_label (bdd_topvar mgr bdd)))in
        let new_weight = (addop (multop highw thnw) (multop loww elsw)) in
        Hashtbl.Poly.add_exn cache ~key:bdd ~data:new_weight;
        new_weight in
  if wmc_type = 2 then (Bignum.of_float_decimal
          (wmc_rec bdd (Hashtbl.Poly.map w hashtable_to_float) (Hashtbl.Poly.create ()) (+.) ( *. ) 1. 0.))
    else if wmc_type = 1 then (wmc_rec bdd w (Hashtbl.Poly.create ()) Bignum.(+) Bignum.( * ) Bignum.one Bignum.zero) 
    else (Bignum.of_float_decimal (LogProbability.conv (wmc_rec bdd 
            (Hashtbl.Poly.map (Hashtbl.Poly.map w hashtable_to_float) hashtable_to_log)
            (Hashtbl.Poly.create ()) (LogProbability.add) (LogProbability.mult) (LogProbability.make 1.) (LogProbability.make 0.))))
      
     

