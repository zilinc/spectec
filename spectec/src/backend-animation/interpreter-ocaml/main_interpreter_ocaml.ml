let basepath = "./src/backend-animation/interpreter-ocaml/build/"

let capsfirst s =
  let first = String.sub s 0 1 in
  let rest = String.sub s 1 (String.length s - 1) in
  String.uppercase_ascii first ^ rest

(* Generate a dune file for the dl_interpreter library *)
let generate_dune_file () =
  let modules = ["dl_codegen"; "dl_codegen_types"; "dl_codegen_util"; "construct_ocaml"] in
  let libraries = ["backend_animation"; "backend_interpreter"] in
  (* Dune file content *)
  let lib_def = Printf.sprintf
    "(include_subdirs no)\n(library\n  (name interpreter_ocaml)\n  (modules %s)\n  (libraries %s))"
    (String.concat " " modules) (String.concat " " libraries)
  in
  let exec_def = Printf.sprintf
    "(executable\n  (name dl_runner)\n  (modules dl_runner)\n  (libraries interpreter_ocaml))"
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

let generate_ocaml dl ocamlfile = 
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
  let main, types, typeconv = Interpreter_ocaml.generate_ocaml dl in
  let type_import = Printf.sprintf "open %s_types\n" (capsfirst ocaml_filename) in
  let util_import = Printf.sprintf "open %s_util\n" (capsfirst ocaml_filename) in
  let sup_redundant = "[@@@ocaml.warning \"-11\"]\n\n" in
  write_file (basepath ^ ocaml_filename ^ ".ml") (sup_redundant ^ type_import ^ util_import ^ main);
  write_file (basepath ^ ocaml_filename ^ "_types.ml") types;
  write_file (basepath ^ ocaml_filename ^ "_util.ml") (sup_redundant ^ type_import ^ typeconv)