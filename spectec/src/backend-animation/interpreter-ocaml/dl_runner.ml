open Interpreter_ocaml.Dl_codegen_types
open Interpreter_ocaml.Dl_codegen
open Interpreter_ocaml.Dl_codegen_util
open Interpreter_ocaml.Construct_ocaml
open Reference_interpreter.Script
open Reference_interpreter.Source
open Reference_interpreter.Run

module Register = Backend_interpreter.Ds.Register(struct type t = moduleinst end)
module Modules = Backend_interpreter.Ds.Register(struct type t = module_ end)

let globalstore = ref {
  uc_tags_store = [];
  uc_globals_store = [];
  uc_mems_store = [];
  uc_tables_store = [];
  uc_funcs_store = [];
  uc_datas_store = [];
  uc_elems_store = [];
  uc_structs_store = [];
  uc_arrays_store = [];
  uc_exns_store = []
}

let int_of_ocamlchar (char : DL.char) : int = match char with
  | DL.C_pct__char n -> n
let string_of_ocamlname = function
  | DL.C_pct__name chars ->
      chars |> List.map int_of_ocamlchar |> Util.Utf8.encode

let externaddr_from_import import = failwith "TODO: implement externaddr_from_import"

let get_export name moduleinst_name =
  let exports = (Register.find moduleinst_name).uc_exports_moduleinst in 
  List.find (fun export -> (string_of_ocamlname export.uc_name_exportinst) = name) exports

let get_export_addr name moduleinst_name =
  let export_addr = get_export name moduleinst_name in
  (*Printf.printf "Getting funcaddr %s from moduleinst %s...\n" name moduleinst_name;*)
  match export_addr.uc_addr_exportinst with
  | DL.FUNC_externaddr funcaddr -> funcaddr
  | _ -> failwith ("Export " ^ name ^ " is not a function.")

(*let get_externaddr import =
  let R.Ast.Import (module_name, item_name, _) = import.it in
  module_name
  |> Utf8.encode
  |> get_export (Utf8.encode item_name)
  |> find_str_field "ADDR"*)

(*let textual_to_module textual =
  match (snd textual).it with
  | R.Script.Textual (m, _) -> m
  | _ -> assert false*)

let get_moduleinst config =
  let state, _ = uncase_config_c_pct__semi_pct__config config in
  let store', frame' = uncase_state_c_pct__semi_pct__state state in 
  globalstore := store';
  frame'.uc_module_frame

let instantiate_helper (m : module_) = 
  let imports = match m with 
  | MODULE_module_ (_, imports, _, _, _, _, _, _, _, _, _) -> imports
  in 
  let externaddrs = List.map externaddr_from_import imports in
  let config' = instantiate !globalstore m externaddrs in 
  get_moduleinst config'

let invoke_helper module_ funcname args = 
  Printf.printf "[Invoking %s...]\n" funcname;
  let funcaddr = get_export_addr funcname module_ in
  invoke !globalstore funcaddr (List.map ocaml_of_literal args)

let run_action action =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    let config' = invoke_helper (Register.get_module_name var_opt) (Util.Utf8.encode funcname) args in 
    uc_steps config'
  | _ -> failwith "TODO: implement other actions"

let test_assertion assertion =
  match assertion.it with
  | AssertReturn (action, expected) ->
    let C_pct__semi_pct__config (_, vals) = run_action action in 
    let result = List.map val_of_ocaml vals in 
    assert_results no_region result expected;
    ()
  | _ -> failwith "TODO: implement other assertions"

let run_command cmd = match cmd.it with 
  | Module (var_opt, def) ->
    Printf.printf "[Defining module %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var_opt);
    def
    |> Backend_animation.Runner.module_of_def
    |> ocaml_of_module
    |> Modules.add_with_var var_opt 
  | Instance (var1_opt, var2_opt) ->
    Printf.printf "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt);
    Modules.find (Modules.get_module_name var2_opt)
    |> instantiate_helper
    |> Register.add_with_var var1_opt
  (*| Action a ->
    ignore (run_action a); success*)
  | Assertion a -> test_assertion a; Printf.printf "[Assertion passed]\n"
  | _ -> failwith "TODO: implement other commands"

let () =
  if Array.length Sys.argv <> 2 then (
    prerr_endline "Usage: program <.wast file>";
    exit 1
  );

  let filename = Sys.argv.(1) in
  let cmds = Backend_animation.Runner.run filename in
  List.iter run_command cmds