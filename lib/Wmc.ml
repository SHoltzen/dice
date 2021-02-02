open Core
open Cudd

type ptr =
    True
  | False
  | Ptr of int

type bddentry = int * ptr * ptr * ((Float.t Option.t) ref)

let rec import tbl (array: bddentry Array.t) (cnt: int ref) bdd : ptr =
  if Bdd.is_true bdd then True
  else if Bdd.is_false bdd then False
  else match Hashtbl.Poly.find tbl bdd with
  | Some(v) -> v
  | None ->
    let (thn, els) = (Bdd.dthen bdd, Bdd.delse bdd) in
    let impthn = import tbl array cnt thn in
    let impels = import tbl array cnt els in
    let cur_cnt = !cnt in
    cnt := !cnt + 1;
    let v = (Bdd.topvar bdd, impthn, impels, ref None) in
    Array.set array cur_cnt v;
    Hashtbl.Poly.add_exn tbl ~key:bdd ~data:(Ptr(cur_cnt));
    Ptr(cur_cnt)

(** map from variable index to (low weight, high weight) *)
type weight = (int, (float*float)) Hashtbl.Poly.t

(** Perform a weighted model count of the BDD `bdd` with weight function `w` *)
let wmc bdd (w: weight) =
  (* internal memoized recursive weighted model count *)
  let numvars = Man.get_bddvar_nb (Bdd.manager bdd) in
  let weight_array =
      let a = Array.init numvars ~f:(fun _ -> 0.0) in
      Hashtbl.Poly.iteri w ~f:(fun ~key ~data:(low, _) ->
          Array.set a key low);
      a in
  Bdd.wmc (Bdd.manager bdd) bdd weight_array

  (* let rec wmc_rec bdd w cache : float=
   *   if Bdd.is_true bdd then 1.0
   *   else if Bdd.is_false bdd then 0.0
   *   else match Hashtbl.Poly.find cache bdd with
   *     | Some v -> v
   *     | _ ->
   *       (\* compute weight of children *\)
   *       let (thn, els) = (Bdd.dthen bdd, Bdd.delse bdd) in
   *       let thnw = wmc_rec thn w cache and
   *         elsw = wmc_rec els w cache in
   *       (\* compute new weight, add to cache *\)
   *       let (loww, highw) = try Hashtbl.Poly.find_exn w (Bdd.topvar bdd)
   *         with _ -> failwith (Format.sprintf "Could not find variable %d" (Bdd.topvar bdd))in
   *       let new_weight = (highw *. thnw) +. (loww *. elsw) in
   *       Hashtbl.Poly.add_exn cache ~key:bdd ~data:new_weight;
   *       new_weight in
   * wmc_rec bdd w (Hashtbl.Poly.create ()) *)

let rec wmc_internal (arr: bddentry Array.t) (w: weight) bdd =
  match bdd with
  | True -> 1.0
  | False -> 0.0
  | Ptr(v) ->
    let (lvl, low, high, v) = Array.get arr v in
    (match !v with
     | Some(r) -> r
     | None ->
       let wmcl = wmc_internal arr w low in
       let wmch = wmc_internal arr w high in
       let (loww, highw) = Hashtbl.Poly.find_exn w lvl in
       let res = wmcl *. loww +. wmch *. highw in
       v := Some(res);
       res)


let rec clear_wmc (arr: bddentry Array.t) bdd  =
  match bdd with
  | True -> ()
  | False -> ()
  | Ptr(v) ->
    let (_, low, high, v) = Array.get arr v in
    (match !v with
     | Some(_) ->
       v := None;
       clear_wmc arr low;
       clear_wmc arr high
     | None -> ()
    )


let multi_wmc (bdd: Bdd.dt) _ (w: weight List.t) =
  Format.printf "starting\n";
  let sz = (Bdd.size bdd) in
  let arr : bddentry Array.t = Array.init ( sz)
      ~f:(fun _ -> (0, True, True, ref None)) in
  let tbl = Hashtbl.Poly.create () in
  Format.printf "converting, size: %d \n" sz;
  flush_all();
  let internal = import tbl arr (ref 0) bdd in

  Format.printf "converted\n";
  flush_all();
  List.map w ~f:(fun w ->
      Format.printf "wmc\n";
      flush_all();
      let r = wmc_internal arr w internal in
      Format.printf "clear\n";
      flush_all();
      clear_wmc arr internal;
      Format.printf "cleared\n";
      r
    )
  (* let m = Bdd.manager bdd in
   * let numvars = Man.get_bddvar_nb m in
   * let weight_array = Array.of_list (List.map w ~f:(fun curw ->
   *     let a = Array.init numvars ~f:(fun _ -> (0.0, 0.0)) in
   *     Hashtbl.Poly.iteri curw ~f:(fun ~key ~data ->
   *         Array.set a key data
   *       );
   *     a
   *   )) in
   * (\* internal memoized recursive weighted model count *\)
   * let num = List.length w in
   * let rec wmc_rec bdd cache : float Array.t =
   *   if Bdd.is_true bdd then Array.init num ~f:(fun _ -> 1.0)
   *   else if Bdd.is_false bdd then Array.init num ~f:(fun _ -> 0.0)
   *   else match Hashtbl.Poly.find cache bdd with
   *     | Some v -> v
   *     | _ ->
   *       (\* compute weight of children *\)
   *       let (thn, els) = (Bdd.dthen bdd, Bdd.delse bdd) in
   *       let thnw =  wmc_rec thn cache and
   *         elsw = wmc_rec els cache in
   *       (\* compute new weight, add to cache *\)
   *       let tv = (Bdd.topvar bdd) in
   *       let probs = Array.map (Array.zip_exn thnw (Array.zip_exn elsw weight_array)) ~f:(fun (thn, (els, w)) ->
   *           let (loww, highw) = Array.get w tv in
   *           (highw *. thn) +. (loww *. els)
   *         ) in
   *       Hashtbl.Poly.add_exn cache ~key:bdd ~data:( probs);
   *       probs in
   * Array.to_list (wmc_rec bdd  tbl) *)
