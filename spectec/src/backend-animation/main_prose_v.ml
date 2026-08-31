open Prose_v
open Il.Ast
open Il.Env
open Util.Source


let text_prose dl ofile =
  let prose = text_prose_script dl in
  let oc = open_out ofile in
  Printf.fprintf oc "%s\n" prose;
  close_out oc;
  ()


let build_prose_rule_hint (env: Il.Env.t) =
  List.filter_map (fun hintdef ->
    match hintdef.it with
    | RuleH (relid', ruleid', hints) ->
      List.find_map (fun hint ->
        if hint.hintid.it = "no_prose" then Some (relid', ruleid') else None
      ) hints
    | _ -> None
  ) env.hints


let inject_prose dl env =
  let no_prose = build_prose_rule_hint env in
  let dl' = Wasm_inject.inject_dl dl env no_prose in
  let _ = Def.string_of_dl_script dl' in
  dl'