let basepath = "./src/backend-animation/interpreter-ocaml/build"

let generate_ocaml dl ocamlfile = 
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
  write_file (basepath ^ ocaml_filename ^ "_typeconv.ml") typeconv