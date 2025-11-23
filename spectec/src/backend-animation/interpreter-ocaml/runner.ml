module R = Reference_interpreter
open Backend_interpreter.Ds
open R.Script
open R.Source

let test_file = "./test-ocaml/sample.wat"
let parser = R.Parse.Script.parse_file

let module_of_def def =
  match def.it with
  | Textual (m, _) -> m
  | Encoded (name, bs) -> failwith "TODO: Encoded module"
  | Quoted (_, s) -> failwith "TODO: Quoted module"

let run_command cmd = match cmd.it with 
  | Module (var_opt, def) ->
    Printf.printf "[Defining module %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var_opt);
    def
    |> module_of_def
    |> Modules.add_with_var var_opt 
  (*| Instance (var1_opt, var2_opt) ->
    Printf.printf "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt);
    Modules.find (Modules.get_module_name var2_opt)
    |> instantiate
    |> Register.add_with_var var1_opt*)
  | _ -> failwith "TODO: implement other commands"

let run_wasm file = 
  let commands = parser file in
  Temp_print.pp_script commands;
  List.iter run_command commands
  
let run () = run_wasm test_file