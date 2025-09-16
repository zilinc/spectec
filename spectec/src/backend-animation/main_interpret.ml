open Def
open Script
open Il_util
open Il.Ast
open Util
open Error
open Backend_interpreter.Construct
module I = Backend_interpreter
module R = Reference_interpreter
open R.Script
open R.Source
(* open R.Ast *)
module A = Al.Ast
module C = Construct


(* Errors *)

module Assert = Reference_interpreter.Error.Make ()
let _error_interpret at msg = Error.error at "interpreter" msg

(* Logging *)

let logging = ref false

let log fmt = Printf.(if !logging then fprintf stderr fmt else ifprintf stderr fmt)



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

let try_run runner target =
  let start_time = Sys.time () in
  let result = runner target in
  result, Sys.time () -. start_time

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
  log "%s took %f ms.\n" name (execution_time *. 1000.)

let get_export name moduleinst_name =
  moduleinst_name
  |> Register.find
  |> find_str_field "EXPORTS"
  |> find_list_elem
    (fun export -> text_to_string (find_str_field "NAME" export) = name)

let get_externaddr import =
  let R.Ast.Import (module_name, item_name, _) = import.it in
  module_name
  |> Utf8.encode
  |> get_export (Utf8.encode item_name)
  |> find_str_field "ADDR"

let textual_to_module textual =
  match (snd textual).it with
  | R.Script.Textual (m, _) -> m
  | _ -> assert false

let get_export_addr name moduleinst_name : exp =
  let vl =
    moduleinst_name
    |> get_export name
    |> find_str_field "ADDR"
    |> args_of_case
  in
  try List.hd vl with Failure _ ->
    failwith ("Function export doesn't contain function address")

let get_global_value module_name globalname : exp (* val *) =
  log "[Getting %s...]\n" globalname;

  let index = get_export_addr globalname module_name in
  index
  |> il_to_nat
  |> nth_of_list (Store.access "GLOBALS")
  |> find_str_field "VALUE"


(** Main functions **)

let instantiate module_ : exp =
  log "[Instantiating module...]\n";

  match C.il_of_module module_, List.map get_externaddr module_.it.imports with
  | exception exn -> raise (I.Exception.Invalid (exn, Printexc.get_raw_backtrace ()))
  | il_module, externaddrs ->
    let store = Store.get () in
    Interpreter.instantiate [ expA store ; expA il_module; listE (t_star "externaddr") externaddrs |> expA ]


let invoke moduleinst_name funcname args : exp =
  log "[Invoking %s %s...]\n" funcname (R.Value.string_of_values args |> Lib.String.shorten);

  let store = Store.get () in
  let funcaddr = get_export_addr funcname moduleinst_name in
  Interpreter.invoke [ expA store; expA funcaddr; il_of_list (t_star "val") C.il_of_value args |> expA ]



(** Wast runner **)

let module_of_def def =
  match def.it with
  | Textual (m, _) -> m
  | Encoded (name, bs) -> R.Decode.decode name bs.it
  | Quoted (_, s) -> R.Parse.Module.parse_string s.it |> textual_to_module

let run_action action =
  match action.it with
  | Invoke (var_opt, funcname, args) ->
    invoke (Register.get_module_name var_opt) (Utf8.encode funcname) (List.map it args)
  | Get (var_opt, globalname) ->
    get_global_value (Register.get_module_name var_opt) (Utf8.encode globalname)

let test_assertion assertion =
  let open R in
  match assertion.it with
  | AssertReturn (action, expected) ->
    let result = run_action action |> Interpreter.exp_to_val |> al_to_list al_to_value in
    Run.assert_results no_region result expected;
    success
  | AssertTrap (action, re) -> (
    try
      let result = run_action action |> Interpreter.exp_to_val in
      Run.assert_message assertion.at "runtime" (Al.Print.string_of_value result |> Util.Lib.String.shorten) re;
      fail
    with I.Exception.Trap -> success
  )
  | AssertUninstantiable (var_opt, re) -> (
    try
      Modules.find (Modules.get_module_name var_opt) |> instantiate |> ignore;
      Run.assert_message assertion.at "instantiation" "module instance" re;
      fail
    with I.Exception.Trap -> success
  )
  | AssertException action ->
    (match run_action action with
    | exception I.Exception.Throw -> success
    | _ -> Assert.error assertion.at "expected exception"
    )
  | AssertInvalid (def, re) when !I.Construct.version = 3 ->
    (match def |> module_of_def |> instantiate |> ignore with
    | exception I.Exception.Invalid _ -> success
    | _ ->
      Run.assert_message assertion.at "validation" "module instance" re;
      fail
    )
  | AssertInvalidCustom (def, re) when !I.Construct.version = 3 ->
    (match def |> module_of_def |> instantiate |> ignore with
    | exception I.Exception.Invalid _ -> success
    | _ ->
      Run.assert_message assertion.at "validation" "module instance" re;
      fail
    )
  (* ignore other kinds of assertions *)
  | _ -> pass

let run_command' command =
  let open R in
  match command.it with
  | Module (var_opt, def) ->
    def
    |> module_of_def
    |> Modules.add_with_var var_opt;
    success
  | Instance (var1_opt, var2_opt) ->
    Modules.find (Modules.get_module_name var2_opt)
    |> instantiate
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

let run_command command =
  let start_time = Sys.time () in
  let result =
    let print_fail at msg = Printf.printf "- Test failed at %s (%s)\n" (string_of_region at) (Lib.String.shorten msg) in
    try
      run_command' command
    with
    | I.Exception.Error (at, msg, step) ->
      let msg' = msg ^ " (interpreting " ^ step ^ " at " ^ Source.string_of_region at ^ ")" in
      command.at |> string_of_region |> print_endline;
      (* error_interpret at msg' *)
      print_fail command.at msg';
      fail
    | I.Exception.Invalid (e, backtrace) ->
      print_fail command.at (Printexc.to_string e);
      Printexc.print_raw_backtrace stdout backtrace;
      fail
    | Register.ModuleNotFound x ->
      print_fail command.at ("Target module(" ^ x ^ ") does not exist or is not instantiated successfully");
      fail
    | e ->
      print_fail command.at (Printexc.to_string e);
      Printexc.print_backtrace stdout;
      fail
  in
  result, Sys.time () -. start_time

let run_wast name script =
  Store.init ();
  (* Intialize spectest *)
  log ("[run_wast...]\n");
  let spectest = il_of_spectest () in
  log "[built `spectest`.]\n";
  Register.add "spectest" spectest;  (* spectest is a `moduleinst`. *)
  log ("[registered `spectec`.]\n");

  let result =
    script
    |> List.map run_command
    |> sum_results_with_time
  in
  print_runner_result name result; result


(** Wasm runner **)

let run_wasm' args module_ =
  Store.init ();
  (* Intialize spectest *)
  log ("[run_wasm'...]\n");
  let spectest = il_of_spectest () in
  log "[built `spectest`.]\n";
  Register.add "spectest" spectest;
  log ("[registered `spectec`.]\n");

  (* Instantiate *)
  module_
  |> instantiate
  |> Register.add_with_var None;
  log ("[instantiated module.]\n");

  (* TODO: Only Int32 arguments/results are acceptable *)
  match args with
  | funcname :: args' ->
    let make_value s = R.Value.Num (I32 (Int32.of_string s)) in

    (* Invoke *)
    invoke (Register.get_module_name None) funcname (List.map make_value args')
    (* Print invocation result. We don't really have to convert it to reference
       interpreter's value type though.
    *)
    |> Interpreter.exp_to_val
    |> al_to_list al_to_value
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
    let x = parser_ file in
    log "[finished parsing.]\n";
    x
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
  Interpreter.dl     := dl;
  Interpreter.il_env := env;
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
