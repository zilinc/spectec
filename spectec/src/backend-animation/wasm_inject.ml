open Il.Ast
open Def
open Util
open Source

module ErrorContext : Lib.LogEntry = struct
  type t = pos * string * string
end

module M = Lib.ExceptLogger(Lib.StringError)(ErrorContext)
open M

let inject_step_pure_clause id osubid cl =
  let DefD (qs, args, exp, prems) = cl.it in
  return cl

let inject_step_read_clause id osubid cl =
  let DefD (qs, args, exp, prems) = cl.it in
  return cl

let inject_step_clause id osubid cl =
  let DefD (qs, args, exp, prems) = cl.it in
  let* a = match args with
  | [arg] ->
    let* a = (match arg.it with
    | ExpA a -> return a
    | _ -> throw ""
    )
    in
    return a
  | _ -> throw "Wrong number of arguments."
  in

  return cl

let inject_clause fid osubid (func_clause: func_clause) : func_clause M.m =
  let (orule_id, cl) = func_clause in
  let* cl' =
    if fid.it == "Step_pure" then
      inject_step_pure_clause fid osubid cl
    else if fid.it == "Step_read" then
      inject_step_read_clause fid osubid cl
    else if fid.it == "Step" then
      inject_step_clause fid osubid cl
    else
      return cl
  in
  return (orule_id, cl')

let inject_fdef (fdef: func_def) = match fdef.it with
  | (id, osubid, ps, t, clauses, opartial) ->
    let (r, ctx) = mapM (inject_clause id osubid) clauses |> run_logger in
    let clauses' = (match r with
    | Error e -> failwith (Lib.StringError.string_of_error e)
    | Ok cls' -> cls'
    )
    in
    (id, osubid, ps, t, clauses', opartial) $ fdef.at

let rec inject_def def = match def with
  | TypeDef _ -> def
  | FuncDef fdef -> FuncDef (inject_fdef fdef)
  | RecDef defs -> RecDef (List.map inject_def defs)

let inject_dl dl = List.map inject_def dl