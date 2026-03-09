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

module RI = Reference_interpreter
module I = Backend_interpreter

(* TEMP DEBUGGING *)
(*let string_of_uc_un = function
  | C_pct__uc_un n -> "C_pct__uc_un (" ^ (string_of_int n) ^ ")"
let string_of_num_ = function
  | Mk_num__0_num_ (_, n) -> "Mk_num__0_num_ (" ^ (string_of_uc_un n) ^ ")"
  | Mk_num__1_num_ _ -> "float num_"
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
  | DL.CONST_instr (nt, n) -> "CONST_instr " ^ (match nt with DL.I32_numtype -> "I32" | _ -> "other") ^ " " ^ (string_of_num_ n)
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
  | DL.MEMORY_dot_COPY_instr _ -> "MEMORY_dot_COPY_instr"
  | DL.MEMORY_dot_FILL_instr _ -> "MEMORY_dot_FILL_instr"
  | DL.MEMORY_dot_GROW_instr _ -> "MEMORY_dot_GROW_instr"
  | DL.MEMORY_dot_SIZE_instr _ -> "MEMORY_dot_SIZE_instr"
  | DL.TABLE_dot_COPY_instr _ -> "TABLE_dot_COPY_instr"
  | DL.TABLE_dot_GROW_instr _ -> "TABLE_dot_GROW_instr"
  | DL.TABLE_dot_SIZE_instr _ -> "TABLE_dot_SIZE_instr"*)
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

let success = 1,1
let pass = 0, 0
let fail = 0, 1 
let print_fail = Backend_animation.Main_interpret_v.print_fail
let string_of_values = Backend_animation.Value.string_of_values

let int_of_ocamlchar (char : DL.char) = match char with
  | DL.C_pct__char n -> Z.to_int n
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
  let C_pct__semi_pct__config (state, instrs) = config in
  let C_pct__semi_pct__state (store', frame') = state in
  globalstore := store';
  frame'.uc_module_frame, instrs

let instantiate_helper (m : module_) = 
  let t1 = Sys.time () in
  Printf.printf "[Instantiating module...]\n";  
  let MODULE_module_ (_, imports, _, _, _, _, _, _, _, _, _) = m in
  let externaddrs = List.map externaddr_from_import imports in
  let config' = instantiate_fn !globalstore m externaddrs in
  let C_pct__semi_pct__config (_, instrs) = config' in
  let config'' = steps_fn config' (Z.of_int 256) in
  let t2 = Sys.time () in
  Printf.printf "instantiate took %f s :)\n" (t2 -. t1);
  get_moduleinst config''

let invoke_helper module_ funcname args =
  let t1 = Sys.time () in
  Printf.printf "[Invoking %s...]\n" funcname;
  let funcaddr = get_export_addr funcname module_ in
  let val_args = List.map (fun lit -> lit.it) args in
  (*let il_args = List.map Backend_animation.Construct.il_of_value val_args in
  let args' = List.map ocaml_of_val_ il_args in*)
  let vl_args = List.map Backend_animation.Construct_v.vl_of_value val_args in
  let args' = List.map ocaml_of_val_ vl_args in
  let result = invoke_fn !globalstore funcaddr args' in
  let result' = steps_fn result (Z.of_int 256) in
  let C_pct__semi_pct__config (state', _) = result' in
  let C_pct__semi_pct__state (store', _) = state' in
  globalstore := store';
  let t2 = Sys.time () in
  Printf.printf "invoke %s took %f s :D\n" funcname (t2 -. t1);
  result'

let run_action action =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    invoke_helper (Register.get_module_name var_opt) (Util.Utf8.encode funcname) args
  | _ -> failwith "TODO: implement other actions"

let test_assertion assertion =
  match assertion.it with
  | AssertReturn (action, expected) ->
    let C_pct__semi_pct__config (_, vals) = run_action action in 
    (*let result_il = List.map il_of_instr vals in
    let result = List.map  Backend_animation.Construct.il_to_value result_il in*)
    let result_vl = List.map vl_of_instr vals in
    let result = List.map  Backend_animation.Construct_v.vl_to_value result_vl in
    assert_results no_region result expected;
    success
  | AssertTrap (action, re) ->
    let C_pct__semi_pct__config (_, vals) = run_action action in
    let result_vl = List.map vl_of_instr vals in
    (match result_vl with
    | [ CaseV ([["TRAP"]], []) ] -> success
    | _ -> print_fail assertion.at "runtime" re (string_of_values ", " result_vl)
    )
  | AssertException action ->
    let C_pct__semi_pct__config (_, vals) = run_action action in
    let result_vl = List.map vl_of_instr vals in
    (match result_vl with
    | [ CaseV ([["REF.EXN_ADDR"];[]], _); CaseV ([["THROW_REF"]], []) ] -> success
    | _ -> print_fail assertion.at "expected exception" "" (string_of_values ", " result_vl)
    )
  | AssertUninstantiable (var_opt, re) ->
    let (moduleinst, instrs) = Modules.find (Modules.get_module_name var_opt) 
    |> Backend_animation.Construct_v.vl_of_module
    |> ocaml_of_module_
    |> instantiate_helper in
    let result_vl = List.map vl_of_instr instrs in
    (match result_vl with
    | [ CaseV ([["TRAP"]], []) ]
    | [ CaseV ([["REF.EXN_ADDR"];[]], _); CaseV ([["THROW_REF"]], []) ] -> success
    | _ -> print_fail assertion.at "instantiation" re (string_of_values ", " result_vl)
    )
  | AssertInvalid (def, re)
  | AssertInvalidCustom (def, re) ->
    (match def |> Backend_animation.Runner.module_of_def |> fun ri_m ->
    Fun.const ri_m (Reference_interpreter.Valid.check_module ri_m) 
    |> Backend_animation.Construct_v.vl_of_module
    |> ocaml_of_module_
    |> instantiate_helper |> ignore with
    | exception RI.Valid.Invalid _ -> success
    | exception I.Exception.Invalid _ -> success
    | _ -> print_fail assertion.at "validation" re "module instance")
  | AssertExhaustion (action, re) ->
    (match run_action action with
    | exception I.Exception.OutOfMemory -> success
    | vs -> print_fail assertion.at "runtime" re ""
    )
  | _ -> pass

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
    (* |> Backend_animation.Construct.il_of_module *)
    |> Backend_animation.Construct_v.vl_of_module
    |> ocaml_of_module_
    |> instantiate_helper |> fst
    |> Register.add_with_var var1_opt;
    success
  (*| Action a ->
    ignore (run_action a); success*)
  | Assertion a -> test_assertion a
  | _ -> failwith "TODO: implement other commands"
  end in 
  res, Sys.time () -. start_time


let tests = ref []
let srcs = ref []

let () =
  if Array.length Sys.argv < 2 then (
    prerr_endline "Usage: program <.wast file>";
    exit 1
  );
  let args = Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  let files = List.concat_map (fun s ->
    if Sys.is_directory s then
      Array.to_list (Sys.readdir s)
      |> List.map (Filename.concat s)
    else [s]
  ) args in
  List.iter (fun f ->
    if Filename.check_suffix f ".wast" then tests := f :: !tests
    else if Filename.check_suffix f ".spectec" then srcs := f :: !srcs
  ) files;
  srcs := List.rev !srcs;
  (* for now im just running the first test file *)
  let filename = List.hd !tests in
  let cmds = Backend_animation.Runner.run filename in
  Printf.printf "src has %d files\n" (List.length !srcs);
  (* instantiate spectest *)
  (*let il_spectest = Backend_animation.Script.il_of_spectest () in
  let ocaml_spectest = ocaml_of_moduleinst il_spectest in
  Register.add "spectest" ocaml_spectest;*)
  let el = List.concat_map Frontend.Parse.parse_file !srcs in
  let il, _ = Frontend.Elab.elab el in
  Il.Valid.valid il;
  let il = Middlend.Sideconditions.transform il in
  let il = Middlend.Typefamilyremoval.transform il in
  Printf.printf "IL has %d defs\n" (List.length il);
  let (env, dl) = Backend_animation.Main_animate.run il false false in
  Printf.printf "dl has %d defs\n" (List.length dl);
  Backend_animation.Valid.valid dl;
  Backend_animation.Interpreter_v.il_env := env;
  Backend_animation.Interpreter_v.dl := dl;

  Printf.printf "Running commands. Interpreter_v env has: %d funcs\n" (List.length !Backend_animation.Interpreter_v.dl);
  List.map run_command cmds 
  |> Backend_animation.Main_interpret.sum_results_with_time
  |> Backend_animation.Main_interpret.print_runner_result filename