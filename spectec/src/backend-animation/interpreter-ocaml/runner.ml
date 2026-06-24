module R = Reference_interpreter

open Backend_interpreter.Ds
open R.Script
open R.Source

module Register_v = State_v.Register

let parser = R.Parse.Script.parse_file

let module_of_def = Main_interpret_v.module_of_def
let spectest_v = 
  State_v.Store.init ();
  State_v.Register.init ();
  Spectest_v.il_of_spectest ()

let parse_args () =
  if Array.length Sys.argv < 2 then (
    prerr_endline "Usage: program <.wast file> <spec dir/files...>";
    exit 1
  );
  let tests = ref [] and srcs = ref [] in
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  let files = List.concat_map (fun s ->
    if Sys.is_directory s then
      Array.to_list (Sys.readdir s)
      |> List.sort String.compare
      |> List.map (Filename.concat s)
    else [s]
  ) args in
  List.iter (fun f ->
    if Filename.check_suffix f ".wast" then tests := f :: !tests
    else if Filename.check_suffix f ".spectec" then srcs := f :: !srcs
  ) files;
  List.rev !tests, List.rev !srcs

let init_pipeline srcs =
  let el = List.concat_map Frontend.Parse.parse_file srcs in
  let il, _ = Frontend.Elab.elab el in
  Il.Valid.valid il;
  let il = Middlend.Sideconditions.transform il in
  let il = Middlend.Typefamilyremoval.transform il in
  let (env, dl) = Main_animate.run il false true in
  Valid.valid dl;
  Interpreter_v.il_env := env;
  Interpreter_v.dl := dl

let get_commands file = 
  let commands = parser file in
  let oc = open_out "parsed.log" in  
    List.iter (fun c -> Printf.fprintf oc "%s\n" (Temp_print.string_of_command c)) commands;
  close_out oc;
  commands
  
let run testfile = Printf.printf "Parsing test file \"%s\"\n%!" testfile; get_commands testfile