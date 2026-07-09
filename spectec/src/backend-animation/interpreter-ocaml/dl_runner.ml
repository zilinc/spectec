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
module A = Backend_animation
module C = A.Construct_v_ocaml

let verbose = ref true
let invalids = ref 0

(* the VL store also contains the "hoststate" which isn't part of the spec so we need to remove it before using the generated VL -> OCaml function *)
let ocaml_of_store' store =
  let A.Value.StrV record = store in
  let record' = List.filter (fun (name, _) -> name <> "HOST") record in
  ocaml_of_store (A.Value.StrV record')

(* the initial ocaml store and spectest before any runner file.
Calling once because `ocaml_of_moduleinst` is slow. *)
let ocaml_store = ocaml_of_store (A.State_v.Store.get ())
let ocaml_spectest = ocaml_of_moduleinst (A.Runner.spectest_v)

(* TEMP DEBUGGING *)
let string_of_uc_un = function
  | CPct_uc_un n -> "C_pct__uc_un (" ^ ")"
let string_of_num_ = function
  | Mk_num__0_num_ (_, n) -> "Mk_num__0_num_ (" ^ (string_of_uc_un n) ^ ")"
  | Mk_num__1_num_ _ -> "float num_"
let string_of_dlinstr = function
  | NOP_instr -> "NOP_instr"
  | UNREACHABLE_instr -> "UNREACHABLE_instr"
  | DROP_instr -> "DROP_instr"
  | SELECT_instr _ -> "SELECT_instr"
  | CALL_instr _ -> "CALL_instr"
  | CALL_REF_instr _ -> "CALL_REF_instr"
  | RETURN_instr -> "RETURN_instr"
  | RETURN_CALL_REF_instr _ -> "RETURN_CALL_REF_instr"
  | THROW_REF_instr -> "THROW_REF_instr"
  | CONST_instr (nt, n) -> "CONST_instr " ^ (match nt with I32_numtype -> "I32" | _ -> "other") ^ " " ^ (string_of_num_ n)
  | BINOP_instr _ -> "BINOP_instr"
  | REF_dot_NULL_instr _ -> "REF_dot_NULL_instr"
  | LOCAL_dot_GET_instr _ -> "LOCAL_dot_GET_instr"
  | TABLE_dot_INIT_instr _ -> "TABLE_dot_INIT_instr"
  | ELEM_dot_DROP_instr _ -> "ELEM_dot_DROP_instr"
  | MEMORY_dot_INIT_instr _ -> "MEMORY_dot_INIT_instr"
  | DATA_dot_DROP_instr _ -> "DATA_dot_DROP_instr"
  | REF_dot_I31_NUM_instr _ -> "REF_dot_I31_NUM_instr"
  | REF_dot_STRUCT_ADDR_instr _ -> "REF_dot_STRUCT_ADDR_instr"
  | REF_dot_ARRAY_ADDR_instr _ -> "REF_dot_ARRAY_ADDR_instr"
  | REF_dot_FUNC_ADDR_instr _ -> "REF_dot_FUNC_ADDR_instr"
  | REF_dot_EXN_ADDR_instr _ -> "REF_dot_EXN_ADDR_instr"
  | REF_dot_HOST_ADDR_instr _ -> "REF_dot_HOST_ADDR_instr"
  | REF_dot_EXTERN_instr _ -> "REF_dot_EXTERN_instr"
  | TRAP_instr -> "TRAP_instr"
  | BR_instr _ -> "BR_instr"
  | LABEL_Pct_lbrackcuPct_rbrackcuPct_instr _ -> "LABEL"
  | FRAME_Pct_lbrackcuPct_rbrackcuPct_instr _ -> "FRAME"
  | MEMORY_dot_COPY_instr _ -> "MEMORY_dot_COPY_instr"
  | MEMORY_dot_FILL_instr _ -> "MEMORY_dot_FILL_instr"
  | MEMORY_dot_GROW_instr _ -> "MEMORY_dot_GROW_instr"
  | MEMORY_dot_SIZE_instr _ -> "MEMORY_dot_SIZE_instr"
  | TABLE_dot_COPY_instr _ -> "TABLE_dot_COPY_instr"
  | TABLE_dot_GROW_instr _ -> "TABLE_dot_GROW_instr"
  | TABLE_dot_SIZE_instr _ -> "TABLE_dot_SIZE_instr"
(* ============ *)

type action_result = Config of config | Values of val_ list

let print_runner_result name result =
  let (num_success, total), execution_time = result in
  let percentage =
    if total = 0 then 100.
    else (float_of_int num_success /. float_of_int total) *. 100.
  in

  let emoji =
    if percentage = 100. then ":D :D"
    else if percentage >= 90. then ":)"
    else ":("
  in

  if name = "Total" then
    Printf.printf "Total [%d/%d] (%.2f%%) %s\n"
      num_success total percentage emoji
  else
    Printf.printf "- %d/%d (%.2f%%) %s\n"
      num_success total percentage emoji;

  Printf.printf "%s took %.5f s.\n\n%!" name execution_time;
  flush stdout

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

let update_store s2 = compose_store !globalstore s2

(* The idea is to go from OCaml -> VL -> RI, since OCaml -> VL is automatic. But, if the value is a reference, then the VL -> RI function will not work since it looks into the VL store, which is not used by the OCaml interpreter. Thus, the OCaml -> RI encoding for refs is manually written. *)
let rec ri_ref_of_ocaml (r : ref) = match r with
    | REF_dot_I31_NUM_ref (CPct_uc_un n) -> (RI.I31.I31Ref (Z.to_int n))
    | REF_dot_NULL_ADDR_ref                -> NullRef
    | REF_dot_STRUCT_ADDR_ref _
    | REF_dot_ARRAY_ADDR_ref _
    | REF_dot_FUNC_ADDR_ref _ ->
      let StrV vl_store = vl_of_store !globalstore in
      (* might not need this anymore
      let vl_store' = ("HOST", ref (A.State_v.HostState.mk_state 0)) :: vl_store in*)
      A.State_v.Store.put (StrV vl_store);
      C.vl_to_ref (vl_of_ref r)
    | REF_dot_HOST_ADDR_ref n              -> RI.Script.HostRef (Z.to_int32 n)
    | REF_dot_EXTERN_ref ref_              -> RI.Extern.ExternRef (ri_ref_of_ocaml ref_)

let ri_of_ocaml (i : instr) = match i with
  | REF_dot_I31_NUM_instr _
  | REF_dot_NULL_ADDR_instr
  | REF_dot_STRUCT_ADDR_instr _
  | REF_dot_ARRAY_ADDR_instr _
  | REF_dot_FUNC_ADDR_instr _
  | REF_dot_HOST_ADDR_instr _
  | REF_dot_EXTERN_instr _ ->  RI.Value.Ref (ri_ref_of_ocaml (ref_of_instr i))
  | _ -> i |> vl_of_instr |> C.vl_to_value

let success = 1,1
let pass = 0, 0
let fail = 0, 1
let print_fail at failtype expected actual =
  print_endline (RI.Source.string_of_region at ^ ": Expected " ^ failtype ^ " failure: " ^ expected ^ ":(");
  print_endline ("Got " ^ actual ^ ":O");
  fail
let string_of_values = A.Value.string_of_values

let int_of_ocamlchar (char : DL.char) = match char with
  | DL.CPct_char n -> Z.to_int n
let string_of_ocamlname = function
  | DL.CPct_name chars ->
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
    | DL.TAG_externaddr    addr
    | DL.GLOBAL_externaddr addr | DL.MEM_externaddr addr
    | DL.TABLE_externaddr  addr | DL.FUNC_externaddr addr -> addr

let externaddr_from_import import =
  let IMPORT_import (moduleinst_name, item_name, _) = import in
  let export = get_export (string_of_ocamlname item_name) (string_of_ocamlname moduleinst_name) in
  export.uc_addr_exportinst

(* todo change this to not use uncase *)
let get_moduleinst config =
  let CPct_semiPct_config (state, instrs) = config in
  let CPct_semiPct_state (store', frame') = state in
  globalstore := store';
  frame'.uc_module_frame, instrs

let get_global_value module_name globalname =
  let export_addr = get_export_addr globalname module_name in
  [(List.nth !globalstore.uc_globals_store (Z.to_int export_addr)).uc_value_globalinst]

let instantiate_helper (m : module_) =
  let t1 = Sys.time () in
  (if !verbose then
  Printf.printf "[Instantiating module...]\n%!");
  let MODULE_module_ (_, imports, _, _, _, _, _, _, _, _, _) = m in
  let externaddrs = List.map externaddr_from_import (uncase_list__cpct imports) in
  let config' = instantiate_fn !globalstore m externaddrs in
  let CPct_semiPct_config (_, instrs) = config' in
  let config'' = reduce_expr_fn config' in
  let t2 = Sys.time () in
  (if !verbose then
  Printf.printf "instantiate took %f s :)\n%!" (t2 -. t1));
  get_moduleinst config''

let lit_to_vl lit =
  match lit.it with
  | ValLit v   -> C.vl_of_value v
  | NullLit ht -> C.vl_of_value (RI.Value.Ref RI.Value.NullRef)

let invoke_helper module_ funcname args =
  let t1 = Sys.time () in
  (if !verbose then
  Printf.printf "[Invoking %s...]\n%!" funcname);
  let funcaddr = get_export_addr funcname module_ in
  let vl_args = List.map lit_to_vl args in
  let args' = List.map ocaml_of_val_ vl_args in
  let result = invoke_fn !globalstore funcaddr args' in
  let result' = reduce_expr_fn result in
  let CPct_semiPct_config (state', _) = result' in
  let CPct_semiPct_state (store', _) = state' in
  globalstore := store';
  let t2 = Sys.time () in
  (if !verbose then
  Printf.printf "invoke %s took %f s :D\n%!" funcname (t2 -. t1));
  result'

let run_action action =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    Config (invoke_helper (Register.get_module_name var_opt) (Util.Utf8.encode funcname) args)
  | Get (var_opt, globalname) ->
    Values (get_global_value (Register.get_module_name var_opt) (Util.Utf8.encode globalname))

let test_assertion assertion =
  match assertion.it with
  | AssertReturn (action, expected) ->
    (match run_action action with
    | Config (CPct_semiPct_config (_, vals)) ->
      let result = List.map ri_of_ocaml vals in
      assert_results no_region result expected;
      success
    | Values val_list ->
      let result = List.map (fun v -> v |> instr_of_val_ |> ri_of_ocaml) val_list in
      assert_results no_region result expected;
      success)
  | AssertTrap (action, re) ->
    let Config (CPct_semiPct_config (_, vals)) = run_action action in
    let result_vl = List.map vl_of_instr vals in
    (match result_vl with
    | [ CaseV ([["TRAP"]], []) ] -> success
    | _ -> print_fail assertion.at "runtime" re (string_of_values ", " result_vl)
    )
  | AssertException action ->
    let Config (CPct_semiPct_config (_, vals)) = run_action action in
    let result_vl = List.map vl_of_instr vals in
    (match result_vl with
    | [ CaseV ([["REF.EXN_ADDR"];[]], _); CaseV ([["THROW_REF"]], []) ] -> success
    | _ -> print_fail assertion.at "expected exception" "" (string_of_values ", " result_vl)
    )
  | AssertUninstantiable (var_opt, re) ->
    let (moduleinst, instrs) = Modules.find (Modules.get_module_name var_opt)
    |> C.vl_of_module
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
    (match def |> A.Runner.module_of_def |> fun ri_m ->
    Fun.const ri_m (Reference_interpreter.Valid.check_module ri_m)
    |> C.vl_of_module
    |> ocaml_of_module_
    |> instantiate_helper |> ignore with
    | exception RI.Valid.Invalid _ -> success
    | exception I.Exception.Invalid _ -> success
    | _ -> print_fail assertion.at "validation" re "module instance")
    (*invalids := !invalids + 1;
    pass*)
  | AssertExhaustion (action, re) ->
    (match run_action action with
    | exception I.Exception.OutOfMemory -> success
    | vs -> print_fail assertion.at "runtime" re ""
    )
  | _ -> pass

let run_command oc cmd =
  let start_time = Sys.time () in
  try
  (let res = begin match cmd.it with
  | Module (var_opt, def) ->
    (if !verbose then
    Printf.printf "[Defining module %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var_opt));
    def
    |> A.Runner.module_of_def
    |> Modules.add_with_var var_opt;
    success
  | Instance (var1_opt, var2_opt) ->
    (if !verbose then
    Printf.printf "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt));
    Modules.find (Modules.get_module_name var2_opt)
    (* |> A.Construct.il_of_module *)
    |> C.vl_of_module
    |> ocaml_of_module_
    |> instantiate_helper |> fst
    |> Register.add_with_var var1_opt;
    success
  | Register (modulename, var_opt) ->
    let moduleinst = Register.find (Register.get_module_name var_opt) in
    Register.add (Util.Utf8.encode modulename) moduleinst;
    pass
  | Action a ->
    ignore (run_action a); success
  | Assertion a -> test_assertion a
  | Meta _ -> pass
  end in
  res, Sys.time () -. start_time)
  with
  | Failure msg ->
    Printexc.print_backtrace oc;
    Printf.printf "unexpected Failure :O\n %s\n" msg;
    fail, Sys.time () -. start_time
  | e ->
    Printexc.print_backtrace oc;
    Printf.printf "unexpected Exception :(\n %s\n" (Printexc.to_string e); fail, Sys.time () -. start_time

let run_wast oc cmds =
  (* initialise spectest and meta-interpreter Store / Registry *)
  A.State_v.Store.init ();
  A.Runner.Register_v.init ();
  A.State_v.HostState.reset_glb_timestamp ();
  A.Runner.Register_v.add "spectest" A.Runner.spectest_v;

  (* initialise ocaml store and registry *)
  globalstore := ocaml_store;
  Register.init();
  Register.add "spectest" ocaml_spectest;

  List.map (run_command oc) cmds

let () =
  Printexc.record_backtrace true

let () =
  let tests, srcs = A.Runner.parse_args () in

  (* initialise meta-interpreter and test files *)
  (* todo: meta-interpeter initialisation may no longer be needed. test without. *)
  A.Animate.allow_partial_animation := true;
  A.Runner.init_pipeline srcs;

  let csv = open_out "results.csv" in
  Printf.fprintf csv "testname,passed,total,time\n";

  let results = List.map (fun testfile ->
    let cmds = A.Runner.run testfile in (* parsing *)
    let oc = open_out "exception.log" in
    let result = run_wast oc cmds
      |> A.Main_interpret_v.sum_results_with_time in
    print_runner_result testfile result;

    let ((num_success, total), _execution_time) = result in
      Printf.fprintf csv "%s,%d/%d,%.2f\n"
        testfile
        num_success
        total
        _execution_time;

    result
  ) tests in

  let total = A.Main_interpret_v.sum_results_with_time
    (List.concat_map (fun (r, t) -> [(r, t)]) results) in
  Printf.printf "Warning: %d AssertInvalids were skipped.\n" !invalids;
  print_runner_result "Total" total
