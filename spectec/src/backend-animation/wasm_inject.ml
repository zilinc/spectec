open Il.Ast
open Il.Free
open Il.Print
open Il.Valid
open Il.Eval
open Il_util
open Def
open Util
open Lib.Fun
open Source
open Xl.Mixop
open Xl.Atom
open Lazy


let verbose : string list = ["no_prose"] (* @ ["debug"; "draft_prose"] *)

let info ?(cat = "default") (lz_msg: string lazy_t) =
  if List.mem cat verbose then print_endline ("[I] " ^ force lz_msg) else ()

let draft_prose = info ~cat:"draft_prose"

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

type primitives = { pop : string; push : string
                  ; pops : string; pushes : string
                  ; run_instr : string; run_next_instr : string; update_state : string
                  ; rhs : string; if_func : string; rel_func : string }

let primitives : primitives = { pop            = "popvalue"
                              ; push           = "pushvalue"
                              ; pops           = "popvalues"
                              ; pushes         = "pushvalues"
                              ; run_instr      = "runinstr"
                              ; run_next_instr = "runnextinstr"
                              ; update_state   = "updatez"
                              ; rhs            = "rhs"
                              ; if_func        = "@if"
                              ; rel_func       = "@rel"
                              }


let il_env : Il.Env.t ref = ref Il.Env.empty
let no_prose : (id * id) list ref = ref []


let t_stack ?(at = no) () = VarT ("stack" $ at, []) $ at
let t_val ?(at = no) () = VarT ("val" $ at, []) $ at
let t_instr ?(at = no) () = VarT ("instr" $ at, []) $ at
let t_store ?(at = no) () = VarT ("store" $ at, []) $ at
let t_frame ?(at = no) () = VarT ("frame" $ at, []) $ at

let t_instrs ?(at = no) () = iterT ~at (t_instr ())
let t_vals ?(at = no) () = iterT ~at (t_val ())

let local_oracle = ref 0
let reset_local_oracle () = local_oracle := 0
let get_local_fresh () =
  let n = !local_oracle in
  local_oracle := (n+1);
  n

let fresh_var () : string =
  let n = get_local_fresh () in
  "__v" ^ string_of_int n

let fresh_stack ?(at = no) () : id * exp =
  let n = get_local_fresh () in
  let v = "__stack" ^ string_of_int n in
  let id = v $ at in
  id, mk_expr at (t_instrs ()) (VarE id)

let global_oracle = ref 0
let reset_global_oracle () = global_oracle := 0
let get_global_fresh () =
  let n = !global_oracle in
  global_oracle := (n+1);
  n

let fresh_fun oname : string =
  let n = get_global_fresh () in
  match oname with
  | None -> "fn_" ^ string_of_int n
  | Some s -> s ^ "_" ^ string_of_int n


let merge_quants env qs1 qs2 : quant list M.m =
  (* A very naïve merging strategy. FIXME: If it correct if a common variable is
     depended by types?
  *)
  let open Il.Eq in
  let* qs2' = foldlM (fun acc q2 ->
    match q2.it with
    | ExpP (x, t) ->
      foldlM (fun ex q1 ->
        match q1.it with
        | ExpP (x', t') when eq_id x x' && not (equiv_typ env t t')
        -> throw ("Binding conflict: variable `" ^ x'.it ^ "` has different types in two branches:\n" ^
                  "  ▹ t1 = " ^ string_of_typ t ^ "\n" ^
                  "  ▹ t2 = " ^ string_of_typ t')
        | _ when eq_param q1 q2 -> return true
        | _ -> return false
      ) false qs1 >>= fun ex -> return (if ex then acc else acc @ [q2])
    | DefP (f, ps, t) ->
      foldlM (fun ex q1 ->
        match q1.it with
        | DefP (f', ps', t') when eq_id f f' && not (eq_list eq_param ps ps' && equiv_typ env t t')
        -> throw ("Binding conflict: definition `" ^ f'.it ^ "` has different types in two branches:\n" ^
                  "  ▹ t1 = " ^ string_of_params ps ^ " -> " ^ string_of_typ t ^ "\n" ^
                  "  ▹ t2 = " ^ string_of_params ps' ^ " -> " ^ string_of_typ t')
        | _ when eq_param q1 q2 -> return true
        | _ -> return false
      ) false qs1 >>= fun ex -> return (if ex then acc else acc @ [q2])
    | TypP  _ | GramP _
    -> return (if List.exists (fun q1 -> eq_param q1 q2) qs1 then acc else (acc @ [q2]))
  ) [] qs2
  in
  return (qs1 @ qs2')


(* ************************************************************************** *)
(*                           Explicate Stack                                  *)
(* ************************************************************************** *)

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

let explicate_step_clause ~rule:step_rule env fid osubid cl nth =
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
  let* state, stack_instr, quant0, estack0, args' =
    if List.mem step_rule [Step; Step_read] then
      (match a.it with
      | CaseE (mixop, ({ it = TupE [s; e]; _ } as tup)) when Value.vl_of_mixop mixop = [[];[";"];[]] ->
        let vstack0, estack0 = fresh_stack ~at:a.at () in
        let args' = [ expA ~at:a.at (CaseE (mixop, TupE [s; estack0] $> tup) $> a) ] in
        return (s, e, ExpP (vstack0, t_instr ()) $ a.at, estack0, args')
      | _ -> throw ("Unexpected argument " ^ string_of_exp a)
      )
    else
      let vstack0, estack0 = fresh_stack ~at:a.at () in
      let args' = [ expA ~at:a.at estack0 ] in
      return (Obj.magic "Step_pure has no input state", a, ExpP (vstack0, t_instr ()) $ a.at, estack0, args')
  in
  let* state', stack_instr' =
    if step_rule = Step then
      (match exp.it with
      | CaseE (mixop, { it = TupE [s; e]; _ }) when Value.vl_of_mixop mixop = [[];[";"];[]] -> return (s, e)
      | _ -> throw ("Unexpected function body: " ^ string_of_exp exp)
      )
    else
      return (Obj.magic "Step_read or Step_pure has no output state", exp)
  in
  (* We symbolically execute the split_stack function at the meta-level. *)
  let* vals, instr = split_stack_lhs env stack_instr in
  let* instrs' = split_stack_rhs env stack_instr' in
  draft_prose (lazy ("[I] Function `" ^ fid ^ "` clause " ^ string_of_int (nth+1) ^ ":"));
  if List.mem step_rule [Step; Step_read] then
    draft_prose (lazy ("  > Initial state: " ^ string_of_exp state));
  draft_prose (lazy ("  > To run instruction: " ^ string_of_exp instr));
  let* () = iterM (function
  | Val   e -> draft_prose (lazy ("  > Pop value " ^ string_of_exp e ^ " from the stack")); return ()
  | Vals  e -> draft_prose (lazy ("  > Pop values " ^ string_of_exp e ^ " from the stack")); return ()
  | Instr e -> throw ("Unexpected instr on the value stack: " ^ string_of_exp e)
  | Nothing -> return ()
  ) vals in
  let quants1, estack1, prems1 = List.fold_left (fun (qs, estack, prs) -> function
  | Val   e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instr (); t_instrs () ] in
               let lhs = tupE ~at:e.at ~note:t [ e; estack' ] in
               let rhs = CallE (primitives.pop $ no, [ expA ~at:estack.at estack ]) $$ estack'.at % t in
               qs @ [ ExpP (vstack', t_instr ()) $ e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Vals  e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instrs (); t_instrs () ] in
               let lhs = tupE ~at:e.at ~note:t [ e; estack' ] in
               let rhs = CallE (primitives.pops $ no, [ expA ~at:estack.at estack ]) $$ estack'.at % t in
               qs @ [ ExpP (vstack', t_instr ()) $ e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Instr e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instr (); t_instrs () ] in
               let lhs = tupE ~at:e.at ~note:t [ e; estack' ] in
               let rhs = CallE (primitives.run_instr $ no, [ expA ~at:estack.at estack ]) $$ estack'.at % t in
               qs @ [ ExpP (vstack', t_instr ()) $ e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Nothing -> qs, estack, prs
  ) ([], estack0, []) (Instr instr :: vals) in
  (* Finally, the input stack has been fully popped. *)
  let pr_stack1 = eqPr estack1 (listE (t_instrs ()) []) in
  draft_prose (lazy ("  > ----------"));
  if step_rule = Step then
    draft_prose (lazy ("  > Final state: " ^ string_of_exp state'));
  List.iter (function
  | Val   e -> draft_prose (lazy ("  > Push value " ^ string_of_exp e ^ " to the stack"))
  | Vals  e -> draft_prose (lazy ("  > Push values " ^ string_of_exp e ^ " to the stack"))
  | Instr e -> draft_prose (lazy ("  > Next, run instruction " ^ string_of_exp e))
  | Nothing -> ()
  ) instrs';
  let quants2, estack2, prems2 = List.fold_left (fun (qs, estack, prs) -> function
  | Val   e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instr (); t_instrs () ] in
               let lhs = estack' in
               let rhs = CallE (primitives.push $ no, [ expA ~at:e.at (tupE ~at:e.at ~note:t [ e; estack ]) ])
                           $$ estack'.at % t_instrs () in
               qs @ [ ExpP (vstack', t_instr ()) $e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Vals  e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instrs (); t_instrs () ] in
               let lhs = estack' in
               let rhs = CallE (primitives.pushes $ no, [ expA ~at:e.at (tupE ~at:e.at ~note:t [ e; estack ]) ])
                           $$ estack'.at % t_instrs () in
               qs @ [ ExpP (vstack', t_instr ()) $e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Instr e -> let vstack', estack' = fresh_stack ~at:e.at () in
               let t = t_tup [ t_instr (); t_instrs () ] in
               let lhs = estack' in
               let rhs = CallE (primitives.run_next_instr $ no, [ expA ~at:e.at (tupE ~at:e.at ~note:t [ e; estack ]) ])
                           $$ estack'.at % t_instrs () in
               qs @ [ ExpP (vstack', t_instr ()) $e.at ], estack', prs @ [ eqPr ~at:e.at lhs rhs ]
  | Nothing -> qs, estack, prs
  ) ([], estack1, []) instrs' in
  (* Finally, the fully pushed output stack is equal to the RHS stack. *)
  let pr_stack2 = eqPr ~at:estack2.at estack2 stack_instr' in
  let qs' = quant0 :: quants1 @ qs @ quants2 in
  let exp' =
    if step_rule = Step then
      (match exp.it with
      | CaseE (mixop, ({ it = TupE [s; e]; _ } as tup)) -> CaseE (mixop , TupE [s; estack2] $> tup) $> exp
      | _ -> assert false
      )
    else
      estack2
  in
  return (DefD (qs', args', exp', prems1 @ [pr_stack1] @ prems @ prems2 @ [pr_stack2]) $> cl)

let explicate_clause env id osubid nth (func_clause: func_clause) : func_clause M.m =
  reset_local_oracle ();
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
      explicate_step_clause ~rule:Step_pure env fid osubid cl nth
    else if id.it = "Step_read" then
      explicate_step_clause ~rule:Step_read env fid osubid cl nth
    else if id.it = "Step" then
      explicate_step_clause ~rule:Step env fid osubid cl nth
    else (
      info ~cat:"not_step" (lazy ("Not a step rule: " ^ id.it));
      return cl
    )
  in
  let* () = drop () in
  return (orule_id, cl')



(* ************************************************************************** *)
(*                              Merge Clauses                                 *)
(* ************************************************************************** *)

let gen_rel_function env fid at qs prem : (dl_def * exp) M.m =
  let fname = fresh_fun (Some fid) in
  let* () = push (at, "when generating rel-function `" ^ primitives.rel_func ^ "/" ^ fname ^ "`") in
  let qs' = qs in  (* FIXME: we can drop unused entries. *)
  let cl_tru = None, DefD (qs', [], boolE ~at true, [prem]) $ at in
  let fndef = FuncDef ((primitives.rel_func $ at, Some (fname $ at), [], boolT ~at (), [cl_tru], Some Partial) $ at) in
  let fncall = CallE (primitives.rel_func ^ "/" ^ fname $ at, []) $$ at % (boolT ~at ()) in
  let* () = drop () in
  return (fndef, fncall)

(* ASSUMES: [e1] and [e2] has equivalent types. *)
let gen_if_function env fid at (qs, cond) (qs1, ths, e1) (qs2, els, e2) : (dl_def list * exp) M.m =
  let fname = fresh_fun (Some fid) in
  let* () = push (at, "when generating if-function `" ^ primitives.if_func ^ "/" ^ fname ^ "`") in
  let* fndefs, cond_exp = match cond.it with
  | IfPr e -> return ([], e)
  | RulePr _ ->
    let* rel_fndef, rel_fncall = gen_rel_function env fid at qs cond in
    return ([rel_fndef], rel_fncall)
  | _ -> throw ("Unsupported type of premise as an if-condition: " ^ string_of_prem cond)
  in
  let fvs = Xl.Gen_free.(free_prem cond ++ free_exp e1 ++ free_exp e2 ++ free_prems ths ++ free_prems els).varid in
  let qs', args' = List.filter_map (fun q -> match q.it with
  | ExpP (x, t) -> if Set.mem x.it fvs then Some (q, varE ~at:x.at ~note:t x.it |> expA ~at:x.at) else None
  | _ -> None
  ) qs |> List.split in  (* FIXME: [qs] is wrong. *)
  let* tru_quants = merge_quants env qs' qs1 in
  let* fls_quants = merge_quants env qs' qs2 in
  let tru_cl = None, DefD (tru_quants, args' @ [expA ~at (boolE ~at true )], e1, ths) $ at in
  let fls_cl = None, DefD (fls_quants, args' @ [expA ~at (boolE ~at false)], e2, els) $ at in
  let cls = [tru_cl; fls_cl] in
  let fndef = FuncDef ((primitives.if_func $ at, Some (fname $ at), qs', e1.note, cls, None) $ at) in
  let fncall = CallE (primitives.if_func ^ "/" ^ fname $ at, args' @ [expA ~at cond_exp]) $$ at % e1.note in
  let* () = drop () in
  return (fndefs @ [fndef], fncall)


let dual_ops op1 op2 : bool =
  match op1, op2 with
  | `EqOp, `NeOp
  | `NeOp, `EqOp
  | `GtOp, `LeOp
  | `GeOp, `LtOp
  | `LtOp, `GeOp
  | `LeOp, `GtOp -> true
  | _, _ -> false

(* A set of rules that two premises are considered to be complementary. *)
let dual_prems p1 p2 : bool =
  match p1.it, p2.it with
  | _, ElsePr -> true
  | IfPr e1, IfPr e2 ->
    (match e1.it, e2.it with
    | CmpE (op1, _ot1, e11, e12) , CmpE (op2, _ot2, e21, e22) 
      when dual_ops op1 op2 && Il.Eq.eq_exp e11 e21 && Il.Eq.eq_exp e12 e22 -> true
    | _, _ -> false
    )
  | _, _ -> false

(* RETURNS: a continuation from the RHS id to a list of premises, where the final return is bound to the RHS id. *)
let rec naive_merge env fid (qs1, prems1, e1) (qs2, prems2, e2) : (quant list * (id -> prem list) * dl_def list) M.m =
  let at = over_region [over_region (prems1 @ prems2 |> List.map at); e1.at; e2.at] in
  let* () = if Il.Eval.equiv_typ env e1.note e2.note |> not then
      throw ("The return types of two clauses do not match:\n" ^
             "  ▹ e1 = " ^ string_of_exp e1 ^ "; t1 = " ^ string_of_typ e1.note ^ "\n" ^
             "  ▹ e2 = " ^ string_of_exp e2 ^ "; t2 = " ^ string_of_typ e2.note)
    else return ()
  in
  match prems1, prems2 with
  | [], [] -> return ([], (fun _ -> []), [])
  | p11::ps1, p21::ps2 when Il.Eq.eq_prem p11 p21 ->
      let* qs, k_ps', defs = naive_merge env fid (qs1, ps1, e1) (qs2, ps2, e2) in
      let* qs' = merge_quants env qs qs1 in  (* [qs] is the merge result of [qs1] and [qs2], so it should never
                                                conflict with [qs1]. [qs1] should contain those bindings in [p11]
                                                which mayn't be in [qs].
                                              *)
      return (qs', (fun rhs -> p11 :: k_ps' rhs), defs)
  | p11::ps1, p21::ps2 when dual_prems p11 p21 ->
    let qs11 = [] in   (* TODO: those in [p11] *)
    let qs1' = qs1 in  (* TODO: exclude [p11] *)
    let qs2' = qs2 in  (* TODO: exclude [p21] *)
    let qs_call = [] in  (* TODO: those in [if_call] *)
    let* (fn_defs, if_call) = gen_if_function env fid at (qs11, p11) (qs1', ps1, e1) (qs2', ps2, e2) in
    return (qs_call, (fun rhs -> [IfPr (eqE ~at (VarE rhs $> if_call) if_call) $ at]), fn_defs)
  | p11::ps1, p21::ps2 ->
    let qs11 = [] in   (* TODO: those in [p11] *)
    let qs1' = qs1 in  (* TODO: exclude [p11] *)
    let qs_call = [] in  (* TODO: those in [if_call] *)
    let* (fn_defs, if_call) = gen_if_function env fid at (qs11, p11) (qs1', ps1, e1) (qs2, p21 :: ps2, e2) in
    return (qs_call, (fun rhs -> [IfPr (eqE ~at (VarE rhs $> if_call) if_call) $ at]), fn_defs)

let rhs_func at t : id -> exp = function id ->
  let ve = VarE id $$ at % t in
  CallE (primitives.rhs $ at, [typA ~at t; expA ~at ve]) $$ at % t

(* ASSUMES: [clauses] is not empty. *)
let merge_func_clauses env id fid (clauses: func_clause list) : (func_clause list * dl_def list) M.m =
  let* () = push (over_region (List.map (snd >.> at) clauses), "when merging function clauses") in
  if List.mem id.it Common.step_relids |> not then return (clauses, []) else
  let* clause', if_defs =
    (match clauses with
    | [] -> assert false
    | [cl] -> return (cl, [])
    | cl1::cl2::cls ->
      let _, { it = DefD (qs1, args1, exp1, prems1); _ } = cl1 in
      let _, { it = DefD (qs2, args2, exp2, prems2); _ } = cl2 in
      let* () = if Il.Eq.eq_list Il.Eq.eq_arg args1 args2 |> not then
          throw ("Arguments do not match:\n" ^
                 "  ▹ args1: " ^ string_of_args args1 ^ "\n" ^
                 "  ▹ args2: " ^ string_of_args args2)
        else return ()
      in
      let* (qs, k_prems, if_defs) = naive_merge env fid (qs1, prems1, exp1) (qs2, prems2, exp2) in
      let v_rhs = fresh_var () $ no in
      let q_rhs = ExpP (v_rhs, exp1.note) $ no in
      let e_rhs = rhs_func (over_region [exp1.at; exp2.at]) exp1.note v_rhs in
      let cl = None, (DefD (q_rhs::qs, args1, e_rhs, k_prems v_rhs)) $ (over_region (List.map (snd >.> at) clauses)) in
      return (cl, if_defs)
    )
  in
  let* () = drop () in
  return ([clause'], if_defs)



(* ************************************************************************** *)
(*                        Inject Wasm-Specific Info                           *)
(* ************************************************************************** *)


let inject_fdef fdef : (func_def * dl_def list) M.m =
  let (id, osubid, ps, t, clauses, opartial) = fdef.it in
  let fid = string_of_funcname id osubid in
  let* () = new_with (fdef.at, "in definition `" ^ fid ^ "`") in
  let* clauses' = mapiM (explicate_clause !il_env id osubid) clauses in
  let* clauses'', if_defs = match clauses' with
  | [] -> return ([], [])
  | _ -> merge_func_clauses !il_env id fid clauses'
  in
  return ((id, osubid, ps, t, clauses'', opartial) $ fdef.at, if_defs)

let rec inject_def def : dl_def list M.m = match def with
  | TypeDef _ -> return [def]
  | FuncDef fdef -> let* fdef', if_defs = inject_fdef fdef in return (if_defs @ [FuncDef fdef'])
  | RecDef defs -> let* defs' = List.concat <$> mapM inject_def defs in return [RecDef defs']

let inject_dl dl (env: Il.Env.t) hints : dl_def list =
  il_env := env;
  no_prose := hints;
  let (r, ctx) = List.concat <$> mapM inject_def dl |> run_logger in
  match r with
  | Ok dl'  -> dl'
  | Error e ->
    print_endline ("[E] Failed to inject Wasm information:");
    print_endline (string_of_ctx_error ctx e);
    dl
