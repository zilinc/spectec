module R = Reference_interpreter
open Backend_interpreter.Ds
open R.Script
open R.Source

let parser = R.Parse.Script.parse_file

let module_of_def def =
  match def.it with
  | Textual (m, _) -> m
  | Encoded (name, bs) -> failwith "TODO: Encoded module"
  | Quoted (_, s) -> failwith "TODO: Quoted module"

let get_commands file = 
  let commands = parser file in
  let oc = open_out "parsed.log" in  
    List.iter (fun c -> Printf.fprintf oc "%s\n" (Temp_print.string_of_command c)) commands;
  close_out oc;
  commands
  
let run testfile = Printf.printf "Parsing test file \"%s\"\n" testfile; get_commands testfile