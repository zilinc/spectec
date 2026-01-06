open Interpreter_ocaml.Dl_codegen_types
open Interpreter_ocaml.Dl_codegen
open Interpreter_ocaml.Dl_codegen_util
(*open Interpreter_ocaml.Construct_ocaml*)
open Interpreter_ocaml.Construct_ocaml_new
open Reference_interpreter.Script
open Reference_interpreter.Source
open Reference_interpreter.Value
open Reference_interpreter.Run

module Register = Backend_interpreter.Ds.Register(struct type t = moduleinst end)
(*module Modules = Backend_interpreter.Ds.Register(struct type t = module_ end)*)
module Modules = Backend_interpreter.Ds.Modules

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

(* --- copied from manual construct_ocaml for now --- *)
let ocaml_of_value (v : value) : val_ =
  match v with
  | Num (I32 n) -> DL.CONST_val_ (DL.I32_numtype, DL.C_pct__uc_un (Int32.to_int n))
  | _ -> failwith "TODO: implement non-I32 values"

let ocaml_of_literal (lit : literal) : val_ =
  ocaml_of_value lit.it

let val_of_ocaml (instr: DL.instr) : value =
  match instr with
  | DL.CONST_instr (nt, num) -> 
    let C_pct__uc_un n = num in 
    begin match nt with 
    | DL.I32_numtype -> Num (I32 (Int32.of_int n))
    | _              -> failwith "TODO: non-I32 const"
    end
  | _ -> failwith "TODO: non-CONST instruction"

(* -------- *)

let get_export name moduleinst_name =
  let exports = (Register.find moduleinst_name).uc_exports_moduleinst in 
  List.find (fun export -> (string_of_ocamlname export.uc_name_exportinst) = name) exports

let get_export_addr name moduleinst_name =
  let export_addr = get_export name moduleinst_name in
  (*Printf.printf "Getting funcaddr %s from moduleinst %s...\n" name moduleinst_name;*)
  match export_addr.uc_addr_exportinst with
  | DL.FUNC_externaddr funcaddr -> funcaddr
  | _ -> failwith ("Export " ^ name ^ " is not a function.")

let externaddr_from_import import = 
  let IMPORT_import (moduleinst_name, item_name, _) = import in 
  let export = get_export (string_of_ocamlname item_name) (string_of_ocamlname moduleinst_name) in 
  export.uc_addr_exportinst

(* todo change this to not use uncase *)
let get_moduleinst config =
  let state, _ = uncase_config_c_pct__semi_pct__config config in
  let store', frame' = uncase_state_c_pct__semi_pct__state state in 
  globalstore := store';
  frame'.uc_module_frame

let instantiate_helper (m : module_) = 
  let t1 = Sys.time () in
  Printf.printf "[Instantiating module...]\n";  
  let MODULE_module_ (_, imports, _, _, _, _, _, _, _, _, _) = m in
  let externaddrs = List.map externaddr_from_import imports in
  let config' = instantiate !globalstore m externaddrs in 
  let t2 = Sys.time () in
  Printf.printf "instantiate took %f s :)\n" (t2 -. t1);
  get_moduleinst config'

let invoke_helper module_ funcname args = 
  let t1 = Sys.time () in
  Printf.printf "[Invoking %s...]\n" funcname;
  let funcaddr = get_export_addr funcname module_ in
  let result = invoke !globalstore funcaddr (List.map ocaml_of_literal args) in
  let t2 = Sys.time () in
  Printf.printf "invoke %s took %f s :)\n" funcname (t2 -. t1);
  result

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
    |> Modules.add_with_var var_opt 
  | Instance (var1_opt, var2_opt) ->
    Printf.printf "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt);
    Modules.find (Modules.get_module_name var2_opt)
    |> Backend_animation.Construct.il_of_module
    |> ocaml_of_module_
    |> instantiate_helper
    |> Register.add_with_var var1_opt
  (*| Action a ->
    ignore (run_action a); success*)
  | Assertion a -> test_assertion a; Printf.printf "[Assertion passed :D]\n"
  | _ -> failwith "TODO: implement other commands"

let () =
  if Array.length Sys.argv <> 2 then (
    prerr_endline "Usage: program <.wast file>";
    exit 1
  );
  let filename = Sys.argv.(1) in
  let cmds = Backend_animation.Runner.run filename in
  (* instantiate spectest *)
  (*let il_spectest = Backend_animation.Script.il_of_spectest () in
  let ocaml_spectest = ocaml_of_moduleinst il_spectest in
  Register.add "spectest" ocaml_spectest;*)
  List.iter run_command cmds