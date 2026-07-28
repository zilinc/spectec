let basepath = "./src/backend-animation/interpreter-ocaml/build/"

let capsfirst s =
  let first = String.sub s 0 1 in
  let rest = String.sub s 1 (String.length s - 1) in
  String.uppercase_ascii first ^ rest

(* Generate a dune file for the dl_interpreter library *)
let generate_dune_file () =
  let modules = ["dl_codegen"; "dl_codegen_types"; "dl_codegen_util"; (*"construct_ocaml";*) "construct_ocaml_new"; "builtin"] in
  let libraries = ["backend_animation"; "backend_interpreter"; "reference_interpreter"; "middlend"] in
  (*let prof = "(preprocess (pps landmarks-ppx --auto))\n  (instrumentation (backend landmarks))" in*)
  let lib_def = Printf.sprintf
    "(include_subdirs no)\n(library\n  (name interpreter_ocaml)\n  (modules %s)\n  (libraries %s))"
    (String.concat " " modules) (String.concat " " libraries)
  in
  let exec_def = Printf.sprintf
    "(executable\n  (name dl_runner)\n  (modules dl_runner)\n  (libraries interpreter_ocaml reference_interpreter middlend))"
  in
  let oc = open_out (basepath ^ "dune") in
  output_string oc (lib_def ^ "\n" ^ exec_def);
  close_out oc

(*let generate_runner () =
  let num_tests = 4 in
  let calls =
  String.concat "; "
    (List.init num_tests (fun i -> Printf.sprintf "Interpreter_ocaml.Dl_codegen.run_tests%d ()" (i+2)))
  in
  let runner_content =
    Printf.sprintf
      "let () =\n\
      \  let results = [ %s ] in\n\
      \  if List.for_all ((=) 1) results then (print_endline \"ALL TESTS PASSED\"; exit 0)\n\
      \  else (print_endline \"SOME TESTS FAILED\"; exit 1)\n\
      let parser = Backend_interpreter.Reference_interpreter.Script.parse_file\n\n\
      let run_wasm file = \n\
      \  let _ = parser file in\n\
      \  ()\n"
      calls
  in
  let oc = open_out (basepath ^ "dl_runner.ml") in
  output_string oc runner_content;
  close_out oc*)

(* translate from numE to int/nat - todo: all these functions should be in a util file with the other things from util_ocaml *)
let basic_types_conv =
  match !Parser_ocaml.backend with
  | Parser_ocaml.IL ->
  "let ($$) = Util.Source.($$)\n\
  let ($) = Util.Source.($)\n\
  let (%) = Util.Source.(%)\n\
  let no = Util.Source.no_region\n\
  let notyp = VarT (\"\" $ no, []) $ no\n\
  let dummy_info = {Xl.Atom.def = \"\"; Xl.Atom.case = \"\"}\n\
  let dummy_atom (a : Xl.Atom.atom') : Xl.Atom.atom = {it = a; at = no; note = dummy_info; mark = false}\n\n\
  let ocaml_of_int (e : exp) : int =\n\
  \  match e.it with\n\
  \  | NumE (`Int i) -> Z.to_int i \n\
  \  | _ -> failwith \"Invalid type: should be a NumE int\"\n\n\
  let ocaml_of_bool (e : exp) : bool =\n\
  \  match e.it with\n\
  \  | BoolE b -> b \n\
  \  | _ -> failwith \"Invalid type: should be a BoolE bool\"\n\n\
  let ocaml_of_nat (e : exp) : DL.nat =\n\
  \  match e.it with\n\
  \  | NumE (`Nat n) -> Z.to_int n \n\
  \  | _ -> failwith \"Invalid type: should be a NumE nat\"\n\n\
  let ocaml_of_rat (e : exp) : float =\n\
  \  match e.it with\n\
  \  | NumE (`Rat r) -> Q.to_float r
  \  | _ -> failwith \"Invalid type: should be a NumE rat\"\n\n\
  let ocaml_of_real (e : exp) : float =\n\
  \  match e.it with\n\
  \  | NumE (`Real r) -> r\n\
  \  | _ -> failwith \"Invalid type: should be a NumE real\"\n\n\
  let ocaml_of_list f (e : exp) =\n\
  \  match e.it with\n\
  \  | ListE es -> List.map f es\n\
  \  | _        -> failwith \"Invalid type: should be a ListE\"\n\n\
  let ocaml_of_opt f (e : exp) =\n\
  \  match e.it with\n\
  \  | OptE es -> Option.map f es\n\
  \  | _       -> failwith \"Invalid type: should be a OptE\"\n\n\
  let ocaml_of_string (e : exp) : string =\n\
  \  match e.it with\n\
  \  | TextE s -> s\n\
  \  | _       -> failwith \"Invalid type: should be a TextE\"\n\n\
  let il_of_list f xs = ListE (List.map f xs) $$ no % notyp\n\
  let il_of_opt f x = match x with None -> OptE None $$ no % notyp | Some v -> OptE (Some (f v)) $$ no % notyp\n\
  let il_of_string s = TextE s $$ no % notyp\n\n\
  let il_of_int (i : int)    : exp = NumE (`Int (Z.of_int i)) $$ no % notyp\n\
  let il_of_nat (n : DL.nat) : exp = NumE (`Nat (Z.of_int n)) $$ no % notyp\n\
  let il_of_rat (r : float)  : exp = NumE (`Rat (Q.of_float r)) $$ no % notyp\n\
  let il_of_real (r : float) : exp = NumE (`Real r) $$ no % notyp\n\n"
  | Parser_ocaml.VL ->
  "let ocaml_of_int (v : value) : DL.int =\n\
  \  match v with\n\
  \  | NumV (`Int i) -> i \n\
  \  | _ -> failwith \"Invalid type: should be a NumV int\"\n\n\
  let ocaml_of_bool (v : value) : bool =\n\
  \  match v with\n\
  \  | BoolV b -> b \n\
  \  | _ -> failwith \"Invalid type: should be a BoolV b\"\n\n\
  let ocaml_of_nat (v : value) : DL.nat =\n\
  \  match v with\n\
  \  | NumV (`Nat n) -> n \n\
  \  | _ -> failwith \"Invalid type: should be a NumV nat\"\n\n\
  let ocaml_of_rat (v : value) : float =\n\
  \  match v with\n\
  \  | NumV (`Rat r) -> Q.to_float r
  \  | _ -> failwith \"Invalid type: should be a NumV rat\"\n\n\
  let ocaml_of_real (v : value) : float =\n\
  \  match v with\n\
  \  | NumV (`Real r) -> r\n\
  \  | _ -> failwith \"Invalid type: should be a NumV real\"\n\n\
  let ocaml_of_list f (v : value) =\n\
  \  match v with\n\
  \  | ListV vs -> List.map f (Array.to_list (!vs))\n\
  \  | _        -> failwith \"Invalid type: should be a ListV\"\n\n\
  let ocaml_of_opt f (v : value) =\n\
  \  match v with\n\
  \  | OptV vs -> Option.map f vs\n\
  \  | _       -> failwith \"Invalid type: should be a OptV\"\n\n\
  let ocaml_of_string (v : value) : string =\n\
  \  match v with\n\
  \  | TextV s -> s\n\
  \  | _       -> failwith \"Invalid type: should be a TextV\"\n\n\
  let vl_of_list f xs = ListV (ref (Array.of_list (List.map f xs)))\n\
  let vl_of_opt f x = match x with None -> OptV None | Some v -> OptV (Some (f v))\n\
  let vl_of_string s = TextV s\n\n\
  let vl_of_int (i : DL.int)    : value = NumV (`Int i)\n\
  let vl_of_nat (n : DL.nat) : value = NumV (`Nat n)\n\
  let vl_of_rat (r : DL.rat)  : value = NumV (`Rat r)\n\
  let vl_of_real (r : float) : value = NumV (`Real r)\n\n\
  let vl_of_bool (b : bool) : value = BoolV b\n"

let num_conv () =
  Printf.sprintf
  "let nat_of_rat (r: rat) : nat = if Q.den r = Z.one then Q.num r else raise SubtypingFailed\n\
  let rat_of_nat (n : nat) : rat = Q.of_bigint n\n\
  let rat_of_int (i : Z.t) : rat = Q.of_bigint i\n"

let generate_ocaml dl ocamlfile =
  Printf.printf "Generating OCaml code...\n";
  generate_dune_file ();
  let ocaml_filename = Option.value ~default:"dl_codegen-0" ocamlfile in
  if not (Sys.file_exists basepath) then
    Sys.mkdir basepath 0o644;
  if not (Sys.is_directory basepath) then
    failwith ("Not a directory: " ^ basepath);
  let write_file filename content =
    let oc = open_out filename in
    output_string oc content;
    close_out oc
  in
  let main, types, typeconv, parser = Interpreter_ocaml.generate_ocaml dl in
  let type_import = Printf.sprintf "open %s_types\n" (capsfirst ocaml_filename) in
  let cons_import = Printf.sprintf "open Construct_ocaml_new\n" in
  let module_types = "module DL = Dl_codegen_types\n" in
  let util_import = Printf.sprintf "open %s_util\n" (capsfirst ocaml_filename) in
  let util_ocaml = Printf.sprintf "open Backend_animation.Util_ocaml\n" in
  let ast_import = "open Il.Ast\nopen Backend_animation.Value\n" in
  (* ignore redundant cases in pattern matching for now *)
  let sup_redundant = "[@@@ocaml.warning \"-11\"]\n" in
  (* ignore warnings that updates re-write all fields in a record *)
  let sup_uselessrec = "[@@@ocaml.warning \"-23\"]\n\n" in
  write_file (basepath ^ ocaml_filename ^ ".ml") (sup_redundant ^ sup_uselessrec ^ type_import ^ util_import ^ cons_import ^ main);
  write_file (basepath ^ ocaml_filename ^ "_types.ml") types;
  write_file (basepath ^ ocaml_filename ^ "_util.ml") (sup_redundant ^ type_import ^ util_ocaml ^ (num_conv ()) ^ typeconv);
  write_file (basepath ^ "construct_ocaml_new.ml") (util_ocaml ^ ast_import ^ "\n" ^ module_types ^ "\n" ^ basic_types_conv ^ parser)

(*let generate_runner inputfile = s
  let cmds = Runner.get_commands inputfile in
  let runner_content =
    Printf.sprintf
      "module Register = Backend_interpreter.Ds.Register(struct type t = module_ end)\n\
      \ module Modules = Backend_interpreter.Ds.Register(struct type t = module_ end)\n\n\
      \ let run_command cmd =\n\
      \  match cmd.it with\n\
      \ | Module (var_opt, def) ->\n\
      \    Printf.printf \"[Defining module %%s...]\\n\" (Option.fold ~none:\"[_]\" ~some:(fun var -> var.it) var_opt);\n\
      \    def\n\
      \  ()\n"
      inputfile
  in
  let oc = open_out (basepath ^ "dl_runner.ml") in
  output_string oc runner_content;
  close_out oc*)
