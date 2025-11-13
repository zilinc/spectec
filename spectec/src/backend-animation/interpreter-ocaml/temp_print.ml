(* Writing my own because I can't find them in the Reference_interpreter module *)

open Printf
open Backend_interpreter
open Reference_interpreter

let string_of_var (v : Script.var) = "$" ^ v.it

let string_of_var_opt (v : Script.var option) = match v with 
  | Some v -> string_of_var v
  | None -> "<none>"

let string_of_literal_list (xs : Script.literal list) =
  sprintf "[%d literal(s)]" (List.length xs)

let string_of_result_list (xs : Script.result list) =
  sprintf "[%d result(s)]" (List.length xs)

let string_of_start_opt (string_of_start : Ast.start option) =
  match string_of_start with
  | None -> "<none>"
  | Some _ -> "<some>"

let string_of_mod_ (m : Ast.module_) =
  sprintf "{\n \
  \ types : [%s];
  \ tags : [%s];
  \ globals : [%s];
  \ memories : [%s];
  \ tables : [%s];
  \ funcs : [%s];
  \ datas : [%s];
  \ elems : [%s];
  \ start : %s;
  \ imports : [%s];
  \ exports : [%s];
}" 
  (String.concat "; " (List.map (fun _ -> "type") m.it.types))
  (String.concat "; " (List.map (fun _ -> "tag") m.it.tags))
  (String.concat "; " (List.map (fun _ -> "global") m.it.globals))
  (String.concat "; " (List.map (fun _ -> "memory") m.it.memories))
  (String.concat "; " (List.map (fun _ -> "table") m.it.tables))
  (String.concat "; " (List.map (fun _ -> "func") m.it.funcs))
  (String.concat "; " (List.map (fun _ -> "data") m.it.datas))
  (String.concat "; " (List.map (fun _ -> "elem") m.it.elems))
  (Option.value ~default:"<none>" (Option.map (fun _ -> "start") m.it.start))
  (String.concat "; " (List.map (fun _ -> "import") m.it.imports))
  (String.concat "; " (List.map (fun _ -> "export") m.it.exports))


let string_of_definition (d : Script.definition) =
  match d.it with
  | Textual (mod_, _) -> sprintf "Textual(mod=%s)" (string_of_mod_ mod_)
  | Encoded _ -> "Encoded"
  | Quoted _  -> "Quoted"

let string_of_action (a : Script.action) =
  match a.it with
  | Invoke (vopt, name, lits) ->
      sprintf "Invoke(mod=%s, name=%s, args=%s)"
        (string_of_var_opt vopt) (Utf8.encode name) (string_of_literal_list lits)
  | Get (vopt, name) ->
      sprintf "Get(mod=%s, name=%s)"
        (string_of_var_opt vopt) (Utf8.encode name)

let string_of_assertion (asrt : Script.assertion) =
  match asrt.it with
  | AssertMalformed (_def, msg) ->
      sprintf "AssertMalformed(%s)" msg
  | AssertMalformedCustom (_def, msg) ->
      sprintf "AssertMalformedCustom(%s)" msg
  | AssertInvalid (_def, msg) ->
      sprintf "AssertInvalid(%s)" msg
  | AssertInvalidCustom (_def, msg) ->
      sprintf "AssertInvalidCustom(%s)" msg
  | AssertUnlinkable (vopt, msg) ->
      sprintf "AssertUnlinkable(mod=%s, %s)" (string_of_var_opt vopt) msg
  | AssertUninstantiable (vopt, msg) ->
      sprintf "AssertUninstantiable(mod=%s, %s)" (string_of_var_opt vopt) msg
  | AssertReturn (act, results) ->
      sprintf "AssertReturn(%s, %s)" (string_of_action act) (string_of_result_list results)
  | AssertException act ->
      sprintf "AssertException(%s)" (string_of_action act)
  | AssertTrap (act, msg) ->
      sprintf "AssertTrap(%s, %s)" (string_of_action act) msg
  | AssertExhaustion (act, msg) ->
      sprintf "AssertExhaustion(%s, %s)" (string_of_action act) msg

let string_of_meta (m : Script.meta) =
  match m.it with
  | Input (vopt, path) ->
      sprintf "Input(ns=%s, path=%s)" (string_of_var_opt vopt) path
  | Output (vopt, sopt) ->
      sprintf "Output(ns=%s, out=%s)" (string_of_var_opt vopt) (Option.value ~default:"<none>" sopt)
  | Script (vopt, _script) ->
      sprintf "Script(ns=%s, <commands>)" (string_of_var_opt vopt)

let string_of_command (c : Script.command) : string =
  match c.it with
  | Module (vopt, defn) ->
      sprintf "Module:\n(%s, %s)" (string_of_var_opt vopt) (string_of_definition defn)
  | Instance (as_opt, of_opt) ->
      sprintf "Instance:\n(as=%s, of=%s)" (string_of_var_opt as_opt) (string_of_var_opt of_opt)
  | Register (name, vopt) ->
      sprintf "Register(name=%s, mod=%s)" (Utf8.encode name) (string_of_var_opt vopt)
  | Action a ->
      sprintf "Action(%s)" (string_of_action a)
  | Assertion asrt ->
      sprintf "Assertion(%s)" (string_of_assertion asrt)
  | Meta m ->
      sprintf "Meta(%s)" (string_of_meta m)

let pp_command (c : Script.command) : unit =
  print_endline (string_of_command c)

let pp_script (cmds : Script.script) : unit =
  List.iter (fun c -> pp_command c; print_endline "--------------------") cmds
