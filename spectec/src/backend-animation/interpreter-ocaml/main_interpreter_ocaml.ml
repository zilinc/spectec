let basepath = "./src/backend-animation/interpreter-ocaml/build/"

let capsfirst s =
  let first = String.sub s 0 1 in
  let rest = String.sub s 1 (String.length s - 1) in
  String.uppercase_ascii first ^ rest

(* Generate a dune file for the dl_interpreter library *)
let generate_dune_file () =
  let modules = ["dl_codegen"; "dl_codegen_types"; "dl_codegen_util"; (*"construct_ocaml";*) "construct_ocaml_new"; "builtin"] in
  let libraries = ["backend_animation"; "backend_interpreter"; "reference_interpreter"] in
  (* Dune file content *)
  let lib_def = Printf.sprintf
    "(include_subdirs no)\n(library\n  (name interpreter_ocaml)\n  (modules %s)\n  (libraries %s))"
    (String.concat " " modules) (String.concat " " libraries)
  in
  let exec_def = Printf.sprintf
    "(executable\n  (name dl_runner)\n  (modules dl_runner)\n  (libraries interpreter_ocaml reference_interpreter))"
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

(* translate from numE to int/nat - todo: these 3 functions should be in a util file with the other things from util_ocaml *)
let basic_types_conv = 
  "let ocaml_of_int (e : exp) : int =\n\
  \  match e.it with\n\
  \  | NumE (`Int i) -> Z.to_int i \n\
  \  | _ -> failwith \"Invalid type: should be a NumE int\"\n\n\
  let ocaml_of_nat (e : exp) : DL.nat =\n\
  \  match e.it with\n\
  \  | NumE (`Nat n) -> Z.to_int n \n\
  \  | _ -> failwith \"Invalid type: should be a NumE nat\"\n\n\
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
  \  | _       -> failwith \"Invalid type: should be a TextE\"\n\n"

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
  let module_types = "module DL = Dl_codegen_types\n" in 
  let util_import = Printf.sprintf "open %s_util\n" (capsfirst ocaml_filename) in
  let util_ocaml = Printf.sprintf "open Backend_animation.Util_ocaml\n" in
  let il_import = "open Il.Ast\n" in
  (* ignore redundant cases in pattern matching for now - todo: probably not this *)
  let sup_redundant = "[@@@ocaml.warning \"-11\"]\n" in
  (* ignore warnings that updates re-write all fields in a record *)
  let sup_uselessrec = "[@@@ocaml.warning \"-23\"]\n\n" in
  write_file (basepath ^ ocaml_filename ^ ".ml") (sup_redundant ^ sup_uselessrec ^ type_import ^ util_import ^ main);
  write_file (basepath ^ ocaml_filename ^ "_types.ml") types;
  write_file (basepath ^ ocaml_filename ^ "_util.ml") (sup_redundant ^ type_import ^ util_ocaml ^ typeconv);
  write_file (basepath ^ "construct_ocaml_new.ml") (util_ocaml ^ il_import ^ "\n" ^ module_types ^ "\n" ^ basic_types_conv ^ parser)

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