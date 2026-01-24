open Def
open Script_v
open State_v
open Il.Ast
open Il.Print
open Value
open Util
open Error
open Lib.Time
open Lib.Fun
open Backend_interpreter.Construct
module I = Backend_interpreter
module R = Reference_interpreter
open R.Script
open R.Source
module C = Construct_v



(* Errors *)

module Assert = Reference_interpreter.Error.Make ()
let _error_interpret at msg = Error.error at "interpreter" msg

(* Logging *)

let logging = ref false

let log fmt = Printf.(if !logging then fprintf stderr fmt else ifprintf stderr fmt)

let print_name n = if n = "" then "[_]" else n


(* Result *)

let success = 1, 1
let fail = 0, 1
let pass = 0, 0

let num_parse_fail = ref 0

(* Excluded test files *)

let is_long_test path =
  List.mem (Filename.basename path)
    [ "memory_copy.wast";
      "memory_fill.wast";
      "memory_grow.wast";
      "call_indirect.wast";
      "return_call.wast";
      "return_call_indirect.wast";
      "return_call_ref.wast"
    ]


(* Helper functions *)

let sum = List.fold_left (+) 0
let sum_float = List.fold_left (+.) 0.

let sum_results l =
  let l1, l2 = List.split l in
  sum l1, sum l2
let sum_results_with_time l =
  let l', times = List.split l in
  sum_results l', sum_float times

let print_runner_result name result =
  let (num_success, total), execution_time = result in
  let percentage =
    if total = 0 then 100.
    else (float_of_int num_success /. float_of_int total) *. 100.
  in

  if name = "Total" then
    Printf.printf "Total [%d/%d] (%.2f%%)\n\n" num_success total percentage
  else
    Printf.printf "- %d/%d (%.2f%%)\n\n" num_success total percentage;
  log "%s took %.5f s.\n" name execution_time

let get_export name moduleinst_name =
  Register.find moduleinst_name
  |> as_str_field "EXPORTS"
  |> find_list_elem
       (fun export -> as_str_field "NAME" export |> as_singleton_case |> as_text_value = name)

let get_externaddr import =
  let R.Ast.Import (module_name, item_name, _) = import.it in
  module_name
  |> Utf8.encode
  |> get_export (Utf8.encode item_name)
  |> as_str_field "ADDR"

let textual_to_module textual =
  match (snd textual).it with
  | R.Script.Textual (m, _) -> m
  | _ -> assert false

let get_export_addr name moduleinst_name : value =
  let vl =
    moduleinst_name
    |> get_export name
    |> as_str_field "ADDR"
    |> as_case_value
  in
  try List.hd vl with Failure _ ->
    failwith ("Function export doesn't contain function address")

let get_global_value module_name globalname : value (* val *) =
  get_export_addr globalname module_name
  |> as_nat_value
  |> nth_of_list (Store.access "GLOBALS")
  |> as_str_field "VALUE"


(** Main functions **)

and instantiate module_ : value * value =
  let t1 = Sys.time () in
  log "[Instantiating module...]\n";
  let il_module = C.vl_of_module module_ in
  let externaddrs = List.map get_externaddr module_.it.imports in
  let store = Store.get () in
  let CaseV (_, [state'; instrs']) = Interpreter_v.instantiate [ valA store ; valA il_module; listV_of_list externaddrs |> valA ] in
  let CaseV (_, [store'; frame']) = state' in
  let StrV [_; (fname, moduleinst)] = frame' in
  assert ("MODULE" = fname);
  (* FIXME(zilinc): Do we keep the store if it returns trap or exception? *)
  Store.put store';
  let t2 = Sys.time () in
  print_endline ("instantiate took " ^ string_of_float (t2 -. t1) ^ " s");
  !moduleinst, instrs'


and invoke moduleinst_name funcname args : value =
  let t1 = Sys.time () in
  log "[Invoking %s in module instance %s...]\n" funcname (print_name moduleinst_name);
  let store = Store.get () in
  let funcaddr = get_export_addr funcname moduleinst_name in
  let CaseV (_, [state'; instrs']) = Interpreter_v.invoke [ valA store; valA funcaddr; vl_of_list C.vl_of_value args |> valA ] in
  let CaseV (_, [store'; _]) = state' in
  (* FIXME(zilinc): Do we keep the store if it returns trap or exception? *)
  Store.put store';
  let t2 = Sys.time () in
  print_endline ("invoke `" ^ funcname ^ "` took " ^ string_of_float (t2 -. t1) ^ " s");
  instrs'


(** Wast runner **)

let module_of_def def =
  match def.it with
  | Textual (m, _) -> m
  | Encoded (name, bs) -> R.Decode.decode name bs.it
  | Quoted (_, s) -> R.Parse.Module.parse_string s.it |> textual_to_module

let run_action action : value =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    invoke (Register.get_module_name var_opt) (Utf8.encode funcname) (List.map it args)
  | Get (var_opt, globalname) ->
    [ get_global_value (Register.get_module_name var_opt) (Utf8.encode globalname) ] |> listV_of_list

let print_fail at failtype expected actual =
  print_endline (R.Source.string_of_region at ^ ": Expected " ^ failtype ^ " failure: " ^ expected);
  print_endline ("Got " ^ actual ^ ".");
  fail

let test_assertion assertion =
  let open R in
  match assertion.it with
  | AssertReturn (action, expected) ->
    let result = run_action action |> as_list_value' |> List.map C.vl_to_value in
    Run.assert_results no_region result expected;
    success
  | AssertTrap (action, re) ->
    let result = run_action action |> as_list_value' in
    (match result with
    | [ CaseV ([["TRAP"]], []) ] -> success
    | _ -> print_fail assertion.at "runtime" re (string_of_values ", " result)
    )
  | AssertException action ->
    let result = run_action action |> as_list_value' in
    (match result with
    | [ CaseV ([["REF.EXN_ADDR"];[]], _); CaseV ([["THROW_REF"]], []) ] -> success
    | _ -> print_fail assertion.at "expected exception" "" (string_of_values ", " result)
    )
  | AssertUninstantiable (var_opt, re) ->
    let (moduleinst, instrs) = Modules.find (Modules.get_module_name var_opt) |> instantiate in
    let result = instrs |> as_list_value' in
    (match result with
    | [ CaseV ([["TRAP"]], []) ]
    | [ CaseV ([["REF.EXN_ADDR"];[]], _); CaseV ([["THROW_REF"]], []) ] -> success
    | _ -> print_fail assertion.at "instantiation" re (string_of_values ", " result)
    )
  | AssertInvalid (def, re)
  | AssertInvalidCustom (def, re) ->
    (match def |> module_of_def |> instantiate |> ignore with
    | exception I.Exception.Invalid _ -> success
    | _ -> print_fail assertion.at "validation" re "module instance"
    )
  (* ignore other kinds of assertions *)
  | _ -> pass

let run_command' command =
  let open R in
  let res = match command.it with
  | Module (var_opt, def) ->
    log "[Defining module %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var_opt);
    def
    |> module_of_def
    |> Modules.add_with_var var_opt;
    success
  | Instance (var1_opt, var2_opt) ->
    log "[Adding moduleinst %s...]\n" (Option.fold ~none:"[_]" ~some:(fun var -> var.it) var1_opt);
    Modules.find (Modules.get_module_name var2_opt)
    |> instantiate |> fst
    |> Register.add_with_var var1_opt;
    success
  | Register (modulename, var_opt) ->
    let moduleinst = Register.find (Register.get_module_name var_opt) in
    Register.add (Utf8.encode modulename) moduleinst;
    pass
  | Action a ->
    ignore (run_action a); success
  | Assertion a -> test_assertion a
  | Meta _ -> pass
  in
  res



let run_command command =
  let start_time = Sys.time () in
  let result =
    let print_fail at msg = Printf.printf "- Test failed at %s: %s\n" (string_of_region at) msg in
    try
      run_command' command
    with
    | e ->
      print_fail command.at (Util.Error.print_exn e);
      Printexc.print_backtrace stdout;
      fail
  in
  result, Sys.time () -. start_time

let run_wast name script =
  Store.init ();
  log ("[run_wast...]\n");
  (* Intialise spectest *)
  let spectest = il_of_spectest () in
  Register.add "spectest" spectest;  (* spectest is a `moduleinst`. *)

  let result =
    script
    |> List.map run_command
    |> sum_results_with_time
  in
  print_runner_result name result; result


(** Wasm runner **)

let run_wasm' args module_ =
  Store.init ();
  log ("[run_wasm'...]\n");
  (* Intialise spectest *)
  let spectest = il_of_spectest () in
  Register.add "spectest" spectest;

  (* Instantiate *)
  module_
  |> instantiate |> fst
  |> Register.add_with_var None;

  (* TODO: Only Int32 arguments/results are acceptable *)
  match args with
  | funcname :: args' ->
    let make_value s = R.Value.Num (I32 (Int32.of_string s)) in

    (* Invoke *)
    invoke (Register.get_module_name None) funcname (List.map make_value args')
    (* Print invocation result. We don't really have to convert it to reference
       interpreter's value type though.
    *)
    |> C.vl_to_list C.vl_to_value
    |> R.Value.string_of_values
    |> Lib.String.shorten
    |> print_endline;
    success
  | [] -> success

let run_wasm args module_ =
  let start_time = Sys.time () in
  let result = run_wasm' args module_ in
  result, Sys.time () -. start_time


(* Wat runner *)

let run_wat = run_wasm


(** Parse **)

let parse_file name parser_ file =
  Printf.printf "===== %s =====\n%!" name;
  log "===========================\n\n%s\n\n" name;

  try
    parser_ file
  with e ->
    let bt = Printexc.get_raw_backtrace () in
    print_endline ("- Failed to parse " ^ name ^ "\n");
    log ("- Failed to parse %s\n") name;
    num_parse_fail := !num_parse_fail + 1;
    Printexc.raise_with_backtrace e bt


(** Runner **)

let rec run_file path args =
  if Sys.is_directory path then
    run_dir path
  else try
    (* Check file extension *)
    match Filename.extension path with
    | ".wast" ->
      let (m1, n1), time1 =
        path
        |> parse_file path R.Parse.Script.parse_file
        |> run_wast path
      in
      let (m2, n2), time2 =
        match args with
        | path' :: args' when Sys.file_exists path -> run_file path' args'
        | path' :: _ -> failwith ("file " ^ path' ^ " does not exist")
        | [] -> pass, 0.0
      in
      (m1 + m2, n1 + n2), time1 +. time2
    | ".wat" ->
      path
      |> parse_file path R.Parse.Module.parse_file
      |> textual_to_module
      |> run_wat args
    | ".wasm" ->
      In_channel.with_open_bin path In_channel.input_all
      |> parse_file path (R.Decode.decode path)
      |> run_wasm args
    | _ -> pass, 0.0
  with R.Decode.Code _ | R.Parse.Syntax _ -> pass, 0.0

and run_dir path =
  path
  |> Sys.readdir
  |> Array.to_list
  |> List.sort compare
  |> List.map (fun filename -> run_file (Filename.concat path filename) [])
  |> sum_results_with_time


(** Entry **)
let run (env: Il.Env.t) (dl: dl_def list) (args : string list) =
  Interpreter_v.dl     := dl;
  Interpreter_v.il_env := env;

  match args with
  | path :: args' when Sys.file_exists path ->
    (* Run file *)
    let result = run_file path args' in

    (* Print result *)
    if Sys.is_directory path then (
      if !num_parse_fail <> 0 then
        print_endline ((string_of_int !num_parse_fail) ^ " parsing fail");
      print_runner_result "Total" result;
    )
  | path :: _ -> failwith ("file " ^ path ^ " does not exist")
  | [] -> failwith "no file to run"
