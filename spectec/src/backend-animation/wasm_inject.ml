open Il.Ast
open Def
open Util
open Source

module ErrorContext : Lib.LogEntry with type t = region * string * string = struct
  type t = region * string * string
  let string_of_log_entry (at, id, msg) = "↳ Definition `" ^ id ^ "`(at " ^ string_of_region at ^ "): " ^ msg
end

module M = Lib.ExceptLogger(Lib.StringError)(ErrorContext)
open M

let string_of_context cs = String.concat "\n" (List.map ErrorContext.string_of_log_entry cs)

let string_of_ctx_error ctx err =
  string_of_context ctx ^ "\n" ^ Lib.StringError.string_of_error err


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
    | _ -> throw ("Unexpected argument " ^ Il.Print.string_of_arg arg)
    )
    in
    return a
  | _ -> throw ("Wrong number of arguments: expected 1, got " ^ string_of_int (List.length args))
  in
  return cl


(*

$f(z; (const i) (get x)) = trap   -- if ...

$f(a) =
  -- if (z, stack) = get_state_stack(a)
  -- if (val_stack, ctrl_stack) = split_stack(stack)
  -- if (const i), val_stack = pop(val_stack)



*)




let inject_clause id osubid nth (func_clause: func_clause) : func_clause M.m =
  let (orule_id, cl) = func_clause in
  let fid = string_of_funcname id osubid in
  let* () = push (cl.at, fid, "in function clause " ^ string_of_int (nth + 1)) in
  let* cl' =
    if id.it == "Step_pure" then
      inject_step_pure_clause fid osubid cl
    else if id.it == "Step_read" then
      inject_step_read_clause fid osubid cl
    else if id.it == "Step" then
      inject_step_clause fid osubid cl
    else
      return cl
  in
  return (orule_id, cl')

let inject_fdef (fdef: func_def) : func_def M.m = match fdef.it with
  | (id, osubid, ps, t, clauses, opartial) ->
    let fid = string_of_funcname id osubid in
    let* () = new_with (fdef.at, fid, "") in
    let* clauses' = mapiM (inject_clause id osubid) clauses in
    return ((id, osubid, ps, t, clauses', opartial) $ fdef.at)

let rec inject_def def : dl_def M.m = match def with
  | TypeDef _ -> return def
  | FuncDef fdef -> let* fdef' = inject_fdef fdef in return (FuncDef fdef')
  | RecDef defs -> let* defs' = mapM inject_def defs in return (RecDef defs')

let inject_dl dl =
  let (r, ctx) = mapM inject_def dl |> run_logger in
  match r with
  | Ok dl'  -> dl'
  | Error e -> failwith (string_of_ctx_error ctx e)