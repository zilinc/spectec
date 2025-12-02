module R = Reference_interpreter
open Backend_interpreter.Ds
open R.Script
open R.Source

let test_file = "./test-ocaml/sample.wast"
let parser = R.Parse.Script.parse_file

let module_of_def def =
  match def.it with
  | Textual (m, _) -> m
  | Encoded (name, bs) -> failwith "TODO: Encoded module"
  | Quoted (_, s) -> failwith "TODO: Quoted module"

let get_commands file = 
  let commands = parser file in
  Temp_print.pp_script commands;
  commands
  
let run () = get_commands test_file