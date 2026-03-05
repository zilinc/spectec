open Interpreter_ocaml.Dl_codegen_types
open Interpreter_ocaml.Dl_codegen
open Interpreter_ocaml.Dl_codegen_util
(*open Interpreter_ocaml.Construct_ocaml*)
open Interpreter_ocaml.Construct_ocaml_new
open Reference_interpreter.Script
open Reference_interpreter.Source
open Reference_interpreter.Value
open Reference_interpreter.Run
open Reference_interpreter.Types

module Register = Backend_interpreter.Ds.Register(struct type t = moduleinst end)
(*module Modules = Backend_interpreter.Ds.Register(struct type t = module_ end)*)
module Modules = Backend_interpreter.Ds.Modules

(* TEMPORARY only for debugging *)
let string_of_dlinstr = function
  | DL.NOP_instr -> "NOP_instr"
  | DL.UNREACHABLE_instr -> "UNREACHABLE_instr"
  | DL.DROP_instr -> "DROP_instr"
  | DL.SELECT_instr _ -> "SELECT_instr"
  | DL.CALL_instr _ -> "CALL_instr"
  | DL.CALL_REF_instr _ -> "CALL_REF_instr"
  | DL.RETURN_instr -> "RETURN_instr"
  | DL.RETURN_CALL_REF_instr _ -> "RETURN_CALL_REF_instr"
  | DL.THROW_REF_instr -> "THROW_REF_instr"
  | DL.CONST_instr _ -> "CONST_instr"
  | DL.BINOP_instr _ -> "BINOP_instr"
  | DL.REF_dot_NULL_instr _ -> "REF_dot_NULL_instr"
  | DL.LOCAL_dot_GET_instr _ -> "LOCAL_dot_GET_instr"
  | DL.TABLE_dot_INIT_instr _ -> "TABLE_dot_INIT_instr"
  | DL.ELEM_dot_DROP_instr _ -> "ELEM_dot_DROP_instr"
  | DL.MEMORY_dot_INIT_instr _ -> "MEMORY_dot_INIT_instr"
  | DL.DATA_dot_DROP_instr _ -> "DATA_dot_DROP_instr"
  | DL.REF_dot_I31_NUM_instr _ -> "REF_dot_I31_NUM_instr"
  | DL.REF_dot_STRUCT_ADDR_instr _ -> "REF_dot_STRUCT_ADDR_instr"
  | DL.REF_dot_ARRAY_ADDR_instr _ -> "REF_dot_ARRAY_ADDR_instr"
  | DL.REF_dot_FUNC_ADDR_instr _ -> "REF_dot_FUNC_ADDR_instr"
  | DL.REF_dot_EXN_ADDR_instr _ -> "REF_dot_EXN_ADDR_instr"
  | DL.REF_dot_HOST_ADDR_instr _ -> "REF_dot_HOST_ADDR_instr"
  | DL.REF_dot_EXTERN_instr _ -> "REF_dot_EXTERN_instr"
  | DL.TRAP_instr -> "TRAP_instr"
  | DL.BR_instr _ -> "BR_instr"
  | DL.LABEL__pct__lbrackcu_pct__rbrackcu_pct__instr _ -> "LABEL"
  | DL.FRAME__pct__lbrackcu_pct__rbrackcu_pct__instr _ -> "FRAME"
(* ============ *)

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
  uc_exns_store = [];
  uc_host_store = HOSTSTATE_hoststate
}

let success = Backend_animation.Main_interpret.success

let int_of_ocamlchar (char : DL.char) : int = match char with
  | DL.C_pct__char n -> n
let string_of_ocamlname = function
  | DL.C_pct__name chars ->
      chars |> List.map int_of_ocamlchar |> Util.Utf8.encode

(* --- copied from manual construct_ocaml for now --- *)
(*let ocaml_of_value (v : value) : val_ =
  match v with
  | Num (I32 n) -> DL.CONST_val_ (DL.I32_numtype, DL.C_pct_num_ (Int32.to_int n))
  | _ -> failwith "TODO: implement non-I32 values"*)

(*let ocaml_of_literal (lit : literal) : val_ =
  ocaml_of_value lit.it*)

let heaptype_of_ocaml = function
  | DL.ANY_heaptype -> AnyHT
  | DL.EQ_heaptype -> EqHT
  | DL.I31_heaptype -> I31HT
  | DL.STRUCT_heaptype -> StructHT
  | DL.ARRAY_heaptype -> ArrayHT
  | DL.NONE_heaptype -> NoneHT
  | DL.FUNC_heaptype -> FuncHT
  | DL.NOFUNC_heaptype -> NoFuncHT
  | DL.EXN_heaptype -> ExnHT
  | DL.NOEXN_heaptype -> NoExnHT
  | DL.EXTERN_heaptype -> ExternHT
  | DL.NOEXTERN_heaptype -> NoExternHT
  | DL.BOT_heaptype -> BotHT
  | DL.C_IDX_heaptype _ -> failwith "TODO: implement C_IDX_heaptype"
  | DL.REC_heaptype _ -> failwith "TODO: implement REC_heaptype"
  | DL.C_DEF_heaptype _ -> failwith "TODO: implement C_DEF_heaptype"

(*let val_of_ocaml (instr: DL.instr) : value =
  match instr with
  | DL.CONST_instr (nt, num) -> 
    let C_pct__uc_un n = num in 
    begin match nt with 
    | DL.I32_numtype -> Num (I32 (Int32.of_int n))
    | _              -> failwith "TODO: non-I32 const"
    end
  | DL.REF_dot_NULL_instr ht  -> Ref (NullRef (heaptype_of_ocaml ht))
  | _ -> failwith (Printf.sprintf "TODO: not const or null ref instr/val: %s" (string_of_dlinstr instr))*)

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
  let C_pct__semi_pct__config (state, _) = config in
  let C_pct__semi_pct__state (store', frame') = state in 
  globalstore := store';
  frame'.uc_module_frame

let instantiate_helper (m : module_) = 
  let t1 = Sys.time () in
  Printf.printf "[Instantiating module...]\n";  
  let MODULE_module_ (_, imports, _, _, _, _, _, _, _, _, _) = m in
  let externaddrs = List.map externaddr_from_import imports in
  let config' = instantiate_fn !globalstore m externaddrs in 
  let t2 = Sys.time () in
  Printf.printf "instantiate took %f s :)\n" (t2 -. t1);
  get_moduleinst config'

let invoke_helper module_ funcname args = 
  let t1 = Sys.time () in
  Printf.printf "[Invoking %s...]\n" funcname;
  let funcaddr = get_export_addr funcname module_ in
  let val_args = List.map (fun lit -> lit.it) args in
  let il_args = List.map Backend_animation.Construct.il_of_value val_args in
  let args' = List.map ocaml_of_val_ il_args in
  let result = invoke_fn !globalstore funcaddr args' in
  let t2 = Sys.time () in
  Printf.printf "invoke %s took %f s :D\n" funcname (t2 -. t1);
  result

let run_action action =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    let config' = invoke_helper (Register.get_module_name var_opt) (Util.Utf8.encode funcname) args in 
    steps_fn config' 256
  | _ -> failwith "TODO: implement other actions"

let test_assertion assertion =
  match assertion.it with
  | AssertReturn (action, expected) ->
    let C_pct__semi_pct__config (_, vals) = run_action action in 
    let result_il = List.map il_of_instr vals in
    let result = List.map  Backend_animation.Construct.il_to_value result_il in 
    assert_results no_region result expected;
    success
  | _ -> failwith "TODO: implement other assertions"

let run_command cmd = 
  let start_time = Sys.time () in
  let res = begin match cmd.it with
  | Module (var_opt, def) ->
    Printf.printf "[Defining module %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var_opt);
    def
    |> Backend_animation.Runner.module_of_def
    |> Modules.add_with_var var_opt;
    success
  | Instance (var1_opt, var2_opt) ->
    Printf.printf "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt);
    Modules.find (Modules.get_module_name var2_opt)
    |> Backend_animation.Construct.il_of_module
    |> ocaml_of_module_
    |> instantiate_helper
    |> Register.add_with_var var1_opt;
    success
  (*| Action a ->
    ignore (run_action a); success*)
  | Assertion a -> test_assertion a
  | _ -> failwith "TODO: implement other commands"
  end in 
  res, Sys.time () -. start_time

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
  List.map run_command cmds 
  |> Backend_animation.Main_interpret.sum_results_with_time
  |> Backend_animation.Main_interpret.print_runner_result filename