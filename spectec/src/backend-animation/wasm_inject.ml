open Il.Ast
open Il.Print
open Il.Valid
open Il.Eval
open Il_util
open Def
open Util
open Source
open Xl.Mixop
open Xl.Atom
open Lazy


let verbose : string list = ["no_prose"] (* @ ["debug"] *)

let info ?(cat = "default") (lz_msg: string lazy_t) =
  if List.mem cat verbose then print_endline ("[I] " ^ force lz_msg) else ()

module ErrorContext : Lib.LogEntry with type t = region * string = struct
  type t = region * string
  let string_of_log_entry (at, msg) = "↳ at " ^ string_of_region at ^ ": " ^ msg
end

module M = Lib.ExceptLogger(Lib.StringError)(ErrorContext)
open M

let string_of_context cs = String.concat "\n" (List.map ErrorContext.string_of_log_entry cs)

let string_of_ctx_error ctx err =
  Lib.StringError.string_of_error err ^ "\n" ^ string_of_context ctx


type config = { mutable state  : exp option
              ; mutable state' : exp option
              ; mutable stack  : exp
              ; mutable stack' : exp
              ; mutable instr  : exp
              ; mutable instr' : exp option
              ; mutable store  : exp option
              ; mutable store' : exp option
              ; mutable frame  : exp option
              ; mutable frame' : exp option
              }

module Map = Map.Make(String)

type primitives = { split_stack : string; split_stack' : string
                  ; pop : string; push : string
                  ; run_instr : string; update_state : string }

let primitives : primitives = { split_stack  = "splitstack"
                              ; split_stack' = "splitstackres"
                              ; pop          = "popvalue"
                              ; push         = "pushvalue"
                              ; run_instr    = "runinstr"
                              ; update_state = "updatez"
                              }


let il_env : Il.Env.t ref = ref Il.Env.empty
let no_prose : (id * id) list ref = ref []


let fresh_oracle = ref 0

let fresh_var : string = let n = !fresh_oracle in
                         fresh_oracle := (n+1);
                         "__v" ^ string_of_int n


let t_stack ?(at = no) () = VarT ("stack" $ at, []) $ at
let t_val ?(at = no) () = VarT ("val" $ at, []) $ at
let t_instr ?(at = no) () = VarT ("instr" $ at, []) $ at
let t_store ?(at = no) () = VarT ("store" $ at, []) $ at
let t_frame ?(at = no) () = VarT ("frame" $ at, []) $ at

let t_instrs ?(at = no) () = iterT ~at (t_instr ())
let t_vals ?(at = no) () = iterT ~at (t_val ())


let chk_instr env exp : exp M.m =
  info ~cat:"debug" (lazy ("chk_instr: " ^ string_of_exp exp));
  match equiv_typ env exp.note (t_instr ()) with
  (* | exception e -> throw ("Failed to check for type equivalence (instr): " ^ Printexc.to_string e) *)
  | false -> throw ("Unexpected type: " ^ string_of_typ exp.note ^ "; expected instr")
  | true -> return exp


let chk_val_instr env exp : exp M.m =
  info ~cat:"debug" (lazy ("chk_val_instr: " ^ string_of_exp exp));
  let* exp' = chk_instr env exp in
  match exp.it with
  | SubE (e, t1, t2) when sub_typ env t1 (t_val ()) -> return exp'
  | CaseE (mixop, _) ->
    let tycases = as_variant_typ env (t_val ()) in
    if List.exists (fun (mixop', _, _) -> Xl.Mixop.eq mixop mixop') tycases then
      return exp'
    else
      throw ("Invalid expression: " ^ string_of_exp exp ^ "; expected a val")
  | CallE (f, args) ->
    (try valid_exp ~side:`Rhs env exp (t_val ()); return exp' with
    | exn -> throw ("Invalid expression: " ^ string_of_exp exp ^ "; expected a val")
    )
  | _ -> throw ("Invalid expression: " ^ string_of_exp exp ^ "; expected a val")

let rec chk_vals_instrs env exp : exp M.m =
  info ~cat:"debug" (lazy ("chk_vals_instrs: " ^ string_of_exp exp));
  let* () = match equiv_typ env exp.note (t_instrs ()) with
  (* | exception e -> throw ("Failed to check for type equivalence (instr*): " ^ Printexc.to_string e) *)
  | false -> throw ("Unexpected expression: " ^ string_of_exp exp ^ "; expected instr* but got " ^ string_of_typ exp.note)
  | true -> return ()
  in
  match exp.it with
  | IterE (e, iterexp) -> (fun x -> IterE (x, iterexp) $> exp) <$> chk_val_instr env e
  | ListE es -> (fun x -> ListE x $> exp) <$> forM es (chk_val_instr env)
  | CatE (e1, e2) -> (fun x y -> CatE (x, y) $> exp) <$> chk_vals_instrs env e1 <*> chk_vals_instrs env e2
  | _ -> throw ("Invalid expression: " ^ string_of_exp exp ^ "; expected vals*")


type instr = Val of exp | Vals of exp | Instr of exp | Nothing

let mk_val x = Val x
let mk_vals xs = Vals xs
let mk_instr x = Instr x

let rec split_instr_from_back env exp : (exp option * instr) M.m =
  info ~cat:"debug" (lazy ("split_instr_from_back: " ^ string_of_exp exp));
  match exp.it with
  | ListE [] -> return (None, Nothing)
  | ListE es ->
    let es1, e2 = Lib.List.split_last es in
    let* instr = catch (mk_val <$> chk_val_instr env e2) (fun _ -> mk_instr <$> chk_instr env e2) in
    return (ListE es1 $> exp |> Option.some, instr)
  | CatE (e1, {it = ListE []; _}) -> split_instr_from_back env e1
  | CatE (e1, ({it = ListE es2; _} as e2)) when List.length es2 > 0 ->
    let es21, e22 = Lib.List.split_last es2 in
    let* instr = catch (mk_val <$> chk_val_instr env e22) (fun _ -> mk_instr <$> chk_instr env e22) in
    let e1' = (match es21 with
    | [] -> e1
    | _ -> CatE (e1, ListE es21 $> e2) $> exp
    )
    in
    return (e1' |> Option.some, instr)
  | CatE (e1, e2) ->
    let* oe2', instr = split_instr_from_back env e2 in
    (match oe2' with
    | Some e2' -> return (CatE (e1, e2') $> exp |> Option.some, instr)
    | None     -> return (Some e1, instr)
    )
  | _ ->
    let* exp' = chk_vals_instrs env exp in
    return (None, Vals exp')

let rec split_instrs_from_back env exp : instr list M.m =
  info ~cat:"debug" (lazy ("split_instrs_from_back: " ^ string_of_exp exp));
  let* oexp', instr = split_instr_from_back env exp in
  match oexp' with
  | Some exp' -> let* instrs = split_instrs_from_back env exp' in
                 return (instr :: instrs)
  | None -> return [instr]

let split_stack_lhs env lhs : (instr list * exp) M.m =
  let* () = push (lhs.at, "in the LHS of %~>%: " ^ string_of_exp lhs) in
  let* lhs', instr =
    (match lhs.it with
    | ListE es when List.length es > 0 ->
      let es1, e2 = Lib.List.split_last es in
      Lib.Fun.curry Fun.id <$> chk_vals_instrs env (ListE es1 $> lhs) <*> chk_instr env e2
    | CatE (e1, ({it = ListE es2; _} as e2)) when List.length es2 > 0 ->
      let es21, e22 = Lib.List.split_last es2 in
      let e1' = (match es21 with
      | [] -> e1
      | _  -> CatE (e1, ListE es21 $> e2) $> lhs
      )
      in
      Lib.Fun.curry Fun.id <$> chk_vals_instrs env e1' <*> chk_instr env e22
    | _ -> throw ("Unexpected expression: " ^ string_of_exp lhs)
    )
  in
  let* vals' = split_instrs_from_back env lhs' in
  let* () = drop () in
  return (vals', instr)

let split_stack_rhs env rhs : instr list M.m =
  let* () = push (rhs.at, "in the RHS of %~>%: " ^ string_of_exp rhs) in
  let* instrs = split_instrs_from_back env rhs in
  let* () = drop () in
  return instrs

type step_rule = Step | Step_read | Step_pure

let inject_step_clause ~rule:step_rule env fid osubid cl nth =
  let DefD (qs, args, exp, prems) = cl.it in
  let env = valid_quants env qs in
  let* a = match args with
  | [arg] ->
    let* a = (match arg.it with
    | ExpA a -> return a
    | _ -> throw ("Unexpected argument " ^ string_of_arg arg)
    )
    in
    return a
  | _ -> throw ("Wrong number of arguments: expected 1, got " ^ string_of_int (List.length args))
  in
  let* state, stack_instr =
    if List.mem step_rule [Step; Step_read] then
      (match a.it with
      | CaseE (mixop, { it = TupE [s; e]; _ }) when Value.vl_of_mixop mixop = [[];[";"];[]] -> return (s, e)
      | _ -> throw ("Unexpected argument " ^ string_of_exp a)
      )
    else
      return (Obj.magic "Step_pure has no input state", a)
  in
  let* state', stack_instr' =
    if step_rule = Step then
      (match exp.it with
      | CaseE (mixop, { it = TupE [s; e]; _ }) when Value.vl_of_mixop mixop = [[];[";"];[]] -> return (s, e)
      | _ -> throw ("Unexpected function body " ^ string_of_exp exp)
      )
    else
      return (Obj.magic "Step_read or Step_pure has no output state", exp)
  in
  (* We symbolically execute the split_stack function at the meta-level. *)
  let* vals, instr = split_stack_lhs env stack_instr in
  let* instrs' = split_stack_rhs env stack_instr' in
  print_endline ("[I] Function `" ^ fid ^ "` clause " ^ string_of_int (nth+1) ^ ":");
  if List.mem step_rule [Step; Step_read] then
    print_endline ("  > Initial state: " ^ string_of_exp state);
  print_endline ("  > To run instruction: " ^ string_of_exp instr);
  let* () = iterM (function
  | Val   e -> print_endline ("  > Push value " ^ string_of_exp e ^ " to the stack"); return ()
  | Vals  e -> print_endline ("  > Push values " ^ string_of_exp e ^ " to the stack"); return ()
  | Instr e -> throw ("Unexpected instr on the value stack: " ^ string_of_exp e)
  | Nothing -> return ()
  ) vals in
  if step_rule = Step then
    print_endline ("  > Final state: " ^ string_of_exp state');
  List.iter (function
  | Val   e -> print_endline ("  > Push value " ^ string_of_exp e ^ " to the stack")
  | Vals  e -> print_endline ("  > Push values " ^ string_of_exp e ^ " to the stack")
  | Instr e -> print_endline ("  > Next, run instruction " ^ string_of_exp e)
  | Nothing -> ()
  ) instrs';
  return cl

let inject_clause env id osubid nth (func_clause: func_clause) : func_clause M.m =
  let (orule_id, cl) = func_clause in
  let fid = string_of_funcname id osubid in
  let* () = push (cl.at, "in clause " ^ string_of_int (nth + 1)) in
  let* cl' =
    if Option.is_some orule_id &&
       List.exists (fun (id', subid') -> Il.Eq.eq_id id id' && Il.Eq.eq_id (Option.get orule_id) subid') !no_prose
    then (
      info ~cat:"no_prose" (lazy ("Suppressed by hint: " ^ id.it ^ "/" ^ (Option.get orule_id).it));
      return cl
    )
    else if id.it = "Step_pure" then
      inject_step_clause ~rule:Step_pure env fid osubid cl nth
    else if id.it = "Step_read" then
      inject_step_clause ~rule:Step_read env fid osubid cl nth
    else if id.it = "Step" then
      inject_step_clause ~rule:Step env fid osubid cl nth
    else (
      info ~cat:"not_step" (lazy ("Not a step rule: " ^ id.it));
      return cl
    )
  in
  let* () = drop () in
  return (orule_id, cl')

let inject_fdef (fdef: func_def) : func_def M.m = match fdef.it with
  | (id, osubid, ps, t, clauses, opartial) ->
    let fid = string_of_funcname id osubid in
    let* () = new_with (fdef.at, "in definition " ^ fid) in
    let* clauses' = mapiM (inject_clause !il_env id osubid) clauses in
    return ((id, osubid, ps, t, clauses', opartial) $ fdef.at)

let rec inject_def def : dl_def M.m = match def with
  | TypeDef _ -> return def
  | FuncDef fdef -> let* fdef' = inject_fdef fdef in return (FuncDef fdef')
  | RecDef defs -> let* defs' = mapM inject_def defs in return (RecDef defs')

let inject_dl dl (env: Il.Env.t) hints =
  il_env := env;
  no_prose := hints;
  let (r, ctx) = mapM inject_def dl |> run_logger in
  match r with
  | Ok dl'  -> dl'
  | Error e ->
    print_endline ("[E] Failed to inject Wasm information:");
    print_endline (string_of_ctx_error ctx e);
    dl
