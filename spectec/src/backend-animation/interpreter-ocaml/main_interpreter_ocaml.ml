let basepath = "./src/backend-animation/interpreter-ocaml/build/"

(* Generate a dune file for the dl_interpreter library *)
let generate_dune_file () =
  let modules = ["dl_codegen"; "dl_codegen_types"; "dl_codegen_util"] in
  let libraries = ["backend_animation"; "xl"] in
  (* Dune file content *)
  let dune_content = Printf.sprintf
    "(include_subdirs no)\n(library\n  (name interpreter_ocaml)\n  (modules %s)\n  (libraries %s))"
    (String.concat " " modules) (String.concat " " libraries)
  in
  let oc = open_out (basepath ^ "dune") in
  output_string oc dune_content;
  close_out oc

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
  write_file (basepath ^ ocaml_filename ^ ".ml") main;
  write_file (basepath ^ ocaml_filename ^ "_types.ml") types;
  write_file (basepath ^ ocaml_filename ^ "_util.ml") typeconv