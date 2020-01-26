open Ocamlbuild_plugin

let () =
  dispatch begin function
  | After_rules ->
     ocaml_lib "mlcuddidl-3.0.4/cudd";
  | _ -> ()
  end
