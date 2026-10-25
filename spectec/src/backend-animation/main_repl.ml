open Def
open Value
open Interpreter_v
open Il.Env
open Il.Ast
open Util.Source


let check_main main_name (fdef: func_def) =
  let (fid, osubid, ps, typ, cls, _) = fdef.it in
  if List.is_empty ps then () else
    raise (Failure ("Main function `" ^ main_name ^ "` must take no arguments."))

let run env dl main_name =
  Interpreter_v.dl     := dl;
  Interpreter_v.il_env := env;
  let main = Def.find_dl_func_def main_name dl |> Option.get in
  check_main main_name main;
  match eval_func main_name main [] |> OptMonad.run_opt with
  | Some result -> print_endline (main_name ^ "> " ^ string_of_value result)
  | None -> print_endline ("REPL: main function `" ^ main_name ^ "` failed to run.")
