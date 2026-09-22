open Il.Ast
open Il.Free
open Il.Subst
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


let verbose : string list = ["no_prose"] (* @ ["debug_merge"; "debug_stack"; "draft_prose"] *)

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


let subst_varid s x =
  match Map.find_opt x.it s.varid with
  | None -> x
  | Some e ->
    (match e.it with
    | VarE x' -> x'
    | _ -> assert false
    )

let subst_quant s p =
  (match p.it with
  | ExpP (x, t) -> ExpP (subst_varid s x, subst_typ s t)
  | TypP x -> TypP x
  | DefP (x, ps, t) ->
    let ps', s' = subst_params s ps in
    DefP (subst_defid s x, ps', subst_typ s' t)
  | GramP (x, ps, t) ->
    let ps', s' = subst_params s ps in
    GramP (x, ps', subst_typ s' t)
  ) $ p.at

let subst_quants s ps = subst_list_dep subst_quant Il.Free.bound_quant s ps



let rec quant_exists env q qs : subst * bool =
  let open Il.Eq in
  match qs with
  | [] -> (empty, false)
  | q'::qs' ->
    (match q.it, q'.it with
    | ExpP (x, t), ExpP (x', t') when eq_id x x' && not (equiv_typ env t t') ->
      let n = get_local_fresh () in
      let x'' = (x.it ^ "_" ^ string_of_int n) $ x.at in
      (* Conflict. There can't be another conflict or another entry that is the same as [q]. *)
      (add_varid empty x (VarE x'' $$ x''.at % t), false)
    | ExpP (x, t), ExpP (x', t') when eq_id x x' ->
      (empty, true)
    | DefP (fid, params, t), DefP (fid', params', t')
      when eq_id fid fid' && not (eq_list eq_param params params' && equiv_typ env t t')->
      (* Conflict. *)
      let n = get_local_fresh () in
      let fid'' = (fid.it ^ "_" ^ string_of_int n) $ fid.at in
      (add_defid empty fid fid'', false)
    | DefP (fid, params, t), DefP (fid', params', t') when eq_id fid fid' ->
      (empty, true)
    | _ -> quant_exists env q qs'
    )

(* Merging is left-biased. It will produce an alpha-renaming for [qs2]. *)
let merge_quants env qs1 qs2 : (quant list * subst * subst) M.m =
  (* A very naïve merging strategy. FIXME: If it correct if a common variable is
     depended by types?
  *)
  let* subst, qs2' = foldlM (fun (subst', qs2') q2 ->
    let subst, ex = quant_exists env q2 qs1 in
    return (union subst subst', if ex then qs2' else qs2' @ [q2])
  ) (empty, []) qs2
  in
  let qs2'', subst' = subst_quants subst qs2' in
  let _ = info ~cat:"debug_merge"
            (lazy ("merge_quants:\n" ^
                   "  ▹ subst = " ^ string_of_subst subst ^ "\n" ^
                   "  ▹ qs2' = " ^ string_of_quants qs2' ^ "\n" ^
                   "  ▹ qs2'' = " ^ string_of_quants qs2''
                  ))
  in
  return (qs1 @ qs2'', subst, subst')

(* Throws an error if conflicting. *)
let merge_compatible_quants env qs1 qs2 : quant list M.m =
  let* qs, s, _ = merge_quants env qs1 qs2 in
  if is_empty s then
    return qs
  else
    throw ("Quantifier lists cannot conflict each other:\n" ^
            "  ▹ qs1 = " ^ string_of_quants qs1 ^ "\n" ^
            "  ▹ qs2 = " ^ string_of_quants qs2)



(* ************************************************************************** *)
(*                           Explicate Stack                                  *)
(* ************************************************************************** *)

let chk_instr env exp : exp M.m =
  info ~cat:"debug_stack" (lazy ("chk_instr: " ^ string_of_exp exp));
  match equiv_typ env exp.note (t_instr ()) with
  (* | exception e -> throw ("Failed to check for type equivalence (instr): " ^ Printexc.to_string e) *)
  | false -> throw ("Unexpected type: " ^ string_of_typ exp.note ^ "; expected instr")
  | true -> return exp

let chk_val_instr env exp : exp M.m =
  info ~cat:"debug_stack" (lazy ("chk_val_instr: " ^ string_of_exp exp));
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
  info ~cat:"debug_stack" (lazy ("chk_vals_instrs: " ^ string_of_exp exp));
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
  info ~cat:"debug_stack" (lazy ("split_instr_from_back: " ^ string_of_exp exp));
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
  info ~cat:"debug_stack" (lazy ("split_instrs_from_back: " ^ string_of_exp exp));
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
  (* Finally, the fully pushed output stack is equal to the RHS stack. But this just repeats
     the same results established by earlier steps.
   *)
  (* let pr_stack2 = eqPr ~at:estack2.at estack2 stack_instr' in *)
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
  return (DefD (qs', args', exp', prems1 @ [pr_stack1] @ prems @ prems2) $> cl)

let explicate_clause env id osubid nth (func_clause: func_clause) : func_clause M.m =
  reset_local_oracle ();
  let (orule_id, cl) = func_clause in
  let fid = string_of_funcname id osubid in
  let* () = push (cl.at, "in clause " ^ string_of_int (nth + 1)) in
  let* cl' =
    if id.it = "Step_pure" then
      explicate_step_clause ~rule:Step_pure env fid osubid cl nth
    else if id.it = "Step_read" then
      explicate_step_clause ~rule:Step_read env fid osubid cl nth
    else if id.it = "Step" then
      explicate_step_clause ~rule:Step env fid osubid cl nth
    else (
      info ~cat:"not_step" (lazy ("Not a step rule: " ^ id.it));
      assert false
    )
  in
  let* () = drop () in
  return (orule_id, cl')



(* ************************************************************************** *)
(*                              Merge Clauses                                 *)
(* ************************************************************************** *)

(* [qs] should contain bindings used by [prem]. *)
let gen_rel_function env fid at qs prem : (exp * dl_def) M.m =
  let fname = fresh_fun (Some fid) in
  let* () = push (at, "when generating rel-function `" ^ primitives.rel_func ^ "/" ^ fname ^ "`") in
  let fvs = Il.Free.(free_prem prem).varid in
  let params, args = List.filter_map (fun q -> match q.it with
  | ExpP (x, t) -> if Set.mem x.it fvs then Some (q, varE ~at:x.at ~note:t x.it |> expA ~at:x.at) else None
  | _ -> None
  ) qs |> List.split in
  let cl_tru = None, DefD (qs, args, boolE ~at true, [prem]) $ at in
  let fndef = FuncDef ((primitives.rel_func $ at, Some (fname $ at), params, boolT ~at (), [cl_tru], Some Partial) $ at) in
  let fncall = CallE (primitives.rel_func ^ "/" ^ fname $ at, []) $$ at % (boolT ~at ()) in
  let* () = drop () in
  return (fncall, fndef)

(* ASSUMES: [e1] and [e2] has equivalent types. *)
let gen_if_function env fid at (qs, cond) (qs1, ths, e1) (qs2, els, e2) : (quant list * exp * dl_def list) M.m =
  let fname = fresh_fun (Some fid) in
  let _ = info ~cat:"debug_merge"
            (lazy ("gen_if_function: `" ^ fname ^ "`\n" ^
                   "  ▹ qs = " ^ string_of_quants qs ^ "\n" ^
                   "  ▹ qs1 = " ^ string_of_quants qs1 ^ "\n" ^
                   "  ▹ qs2 = " ^ string_of_quants qs2
                  ))
  in
  let* () = push (at, "when generating if-function `" ^ primitives.if_func ^ "/" ^ fname ^ "`") in
  let* fndefs, cond_exp = match cond.it with
  | IfPr e -> return ([], e)
  | RulePr _ ->
    let* rel_fncall, rel_fndef = gen_rel_function env fid at qs cond in  (* FIXME: [qs] may contain entries not mentioned in [cond]. *)
    return ([rel_fndef], rel_fncall)
  | _ -> throw ("Unsupported type of premise as an if-condition: " ^ string_of_prem cond)
  in
  (* [qs] can't conflict with [qs1], but it may with [qs2], because the if-condition is often taken from the first clause. *)
  let* tru_quants = merge_compatible_quants env qs qs1 in
  let* fls_quants, fls_s, fls_s' = merge_quants env qs qs2 in
  let* all_quants = merge_compatible_quants env tru_quants fls_quants in
  let e2' = subst_exp fls_s e2 in
  let els' = subst_prems fls_s els in
  let fvs = Il.Free.(free_prem cond ++ free_exp e1 ++ free_exp e2' ++ free_prems ths ++ free_prems els').varid in
  let params, args = List.filter_map (fun q -> match q.it with
  | ExpP (x, t) -> if Set.mem x.it fvs then Some (q, varE ~at:x.at ~note:t x.it |> expA ~at:x.at) else None
  | _ -> None
  ) all_quants |> List.split in
  let tru_cl = None, DefD (tru_quants,                   args @ [expA ~at (boolE ~at true )],                  e1 ,                    ths ) $ at in
  let fls_cl = None, DefD (fls_quants, subst_args fls_s' args @ [expA ~at (boolE ~at false)], subst_exp fls_s' e2', subst_prems fls_s' els') $ at in
  let cls = [tru_cl; fls_cl] in
  let fndef = FuncDef ((primitives.if_func $ at, Some (fname $ at), params @ [ExpP ("_" $ at, boolT ~at ()) $ at], e1.note, cls, None) $ at) in
  let fncall = CallE (primitives.if_func ^ "/" ^ fname $ at, args @ [expA ~at cond_exp]) $$ at % e1.note in
  let* () = drop () in
  return (all_quants, fncall, fndefs @ [fndef])


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

let contains_if_calls e : bool =
  let open Il.Walk in
  let if_collector: bool collector = {
    default         = false;
    compose         = (||);
    collect_exp     = (fun e -> match e.it with
                                | CallE (fid, _) -> (String.starts_with ~prefix:primitives.if_func fid.it, true)
                                | _ -> (false, true));
    collect_prem    = (fun _ -> (false, true));
    collect_iterexp = (fun _ -> (false, true));
    collect_typ     = (fun _ -> (false, true));
    collect_arg     = (fun _ -> (false, true));
  } in
  Il.Walk.collect_exp if_collector e

let rhs_func at t : id -> exp = function id ->
  let ve = VarE id $$ at % t in
  CallE (primitives.rhs $ at, [typA ~at t; expA ~at ve]) $$ at % t

(* FIXME: This function won't work for 3 or more way branching. *)
(* RETURNS: a continuation from the RHS id to a list of premises, where the final return is bound to the RHS id. *)
let rec naive_merge env fid (qs1, prems1, e1) (qs2, prems2, e2) : (quant list * (exp -> prem list) * dl_def list) M.m =
  let _ = info ~cat:"debug_merge"
            (lazy ("naive_merge:\n" ^
                   "  ▹ qs1 = " ^ string_of_quants qs1 ^ "\n" ^
                   "  ▹ qs2 = " ^ string_of_quants qs2
                  ))
  in
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
    return (qs, (fun rhs -> p11 :: k_ps' rhs), defs)
  | p11::ps1, p21::ps2 when dual_prems p11 p21 ->
    let qs11 = qs1 in  (* TODO: those in [p11] *)
    let qs1' = qs1 in  (* TODO: exclude [p11] *)
    let qs2' = qs2 in  (* TODO: exclude [p21] *)
    let* (qs_call, if_call, fn_defs) = gen_if_function env fid at (qs11, p11) (qs1', ps1, e1) (qs2', ps2, e2) in
    return (qs_call, (fun rhs -> [IfPr (eqE ~at rhs if_call) $ at]), fn_defs)
  | p11::ps1, p21::ps2 ->
    let qs11 = qs1 in  (* TODO: those in [p11] *)
    let qs1' = qs1 in  (* TODO: exclude [p11] *)
    let* (qs_call, if_call, fn_defs) = gen_if_function env fid at (qs11, p11) (qs1', ps1, e1) (qs2, p21 :: ps2, e2) in
    return (qs_call, (fun rhs -> [IfPr (eqE ~at rhs if_call) $ at]), fn_defs)

(* ASSUMES: Neither list is empty. *)
let rec score_merge prems1 prems2 : int =
  match prems1, prems2 with
  | [], _ | _, [] -> assert false
  | p11::ps1, p21::ps2 ->
    (match p11.it, p21.it with
    | _ when Il.Eq.eq_prem p11 p21 -> 100 + score_merge ps1 ps2
    | _ when dual_prems p11 p21 -> 90
    | IfPr e1, _ when contains_if_calls e1 -> 0
    | _, IfPr e2 when contains_if_calls e2 -> 0
    | _ -> 10
    )

let rec select_merge_func_clauses env fid clauses : (func_clause list * dl_def list) M.m =
  if List.is_empty clauses then throw ("No clause to merge") else
  if List.length clauses = 1 then return (clauses, []) else

  let module IntPair = struct
    type t = int * int
    let compare (i11, i12) (i21, i22) = Stdlib.(let r1 = compare i11 i21 in if r1 <> 0 then r1 else compare i21 i22)
  end in
  let module IIM = Stdlib.Map.Make(IntPair) in
  let score_table : int IIM.t =
    List.mapi (fun i (_, { it = DefD (_, _, _, prems); _ }) ->
      List.mapi (fun j (_, { it = DefD (_, _, _, prems'); _ }) ->
        ((i, j), score_merge prems prems')
      ) (List.drop (i+1) clauses)
    ) clauses |> List.concat |> IIM.of_list
  in
  assert (IIM.cardinal score_table = let l = List.length clauses in l * (l - 1) / 2);
  let p, top_score = IIM.fold (fun k v ((_, max) as acc) ->
    if v > max then (k, v) else acc
  ) score_table ((0, 0), -1) in
  let _, picked, clauses' = List.fold_left (fun (idx, choose, keep) cl ->
    if fst p = idx || snd p = idx then (idx+1, choose@[cl], keep)
                                  else (idx+1, choose, keep@[cl])
  ) (0, [], []) clauses in
  assert (List.length picked = 2);
  let _, { it = DefD (qs1, args1, e1, prems1); at = at1; _ } = List.nth picked 0 in
  let _, { it = DefD (qs2, args2, e2, prems2); at = at2; _ } = List.nth picked 1 in
  let at = over_region [at1; at2] in
  let* () = push (at, "when merging the " ^ string_of_int (fst p) ^ " and " ^ string_of_int (snd p) ^ "clauses with a score of " ^ string_of_int top_score) in
  let* () = if Il.Eq.eq_list Il.Eq.eq_arg args1 args2 |> not then
      throw ("Arguments do not match:\n" ^
             "  ▹ args1: " ^ string_of_args args1 ^ "\n" ^
             "  ▹ args2: " ^ string_of_args args2)
    else return ()
  in
  let* qs, k_prems, defs = naive_merge env fid (qs1, prems1, e1) (qs2, prems2, e2) in
  let v_rhs = fresh_var () $ no in
  let q_rhs = ExpP (v_rhs, e1.note) $ no in
  let e_rhs = rhs_func (over_region [e1.at; e2.at]) e1.note v_rhs in
  (* Recursive call. *)
  let* clauses'', defs' = select_merge_func_clauses env fid ((None, DefD (q_rhs::qs, args1, e_rhs, k_prems e_rhs) $ at) :: clauses') in
  return (clauses'', defs@defs')


(* ASSUMES: [clauses] is not empty. *)
let rec naive_merge_func_clauses env fid (clauses: func_clause list) : (func_clause list * dl_def list) M.m =
  let* () = push (over_region (List.map (snd >.> at) clauses), "when merging function clauses") in
  let* clauses', if_defs =
    (match clauses with
    | [] -> assert false
    | [cl] -> return ([cl], [])
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
      let cl = None, (DefD (q_rhs::qs, args1, VarE v_rhs $> e_rhs, k_prems e_rhs)) $ (over_region (List.map (snd >.> at) clauses)) in
      let* cls', if_defs' = naive_merge_func_clauses env fid (cl::cls) in  (* Recurse, BAD!!! *)
      return (cls', if_defs @ if_defs')
    )
  in
  let* () = drop () in
  return (clauses', if_defs)



(* ************************************************************************** *)
(*                        Inject Wasm-Specific Info                           *)
(* ************************************************************************** *)


let inject_fdef fdef : (func_def * dl_def list) M.m =
  let (id, osubid, ps, t, clauses, opartial) = fdef.it in
  let fid = string_of_funcname id osubid in
  let* () = new_with (fdef.at, "in definition `" ^ fid ^ "`") in
  (* If not a Step* rule, we don't do anything. *)
  if List.mem id.it Common.step_relids |> not then return (fdef, []) else
  (* If a Step* rule, we filter out the clauses that are marked `no_prose`. *)
  let clauses' = List.filter (fun cl ->
    let orule_id, _ = cl in
    if Option.is_some orule_id &&
       List.exists (fun (id', subid') -> Il.Eq.eq_id id id' && Il.Eq.eq_id (Option.get orule_id) subid') !no_prose
    then (
      info ~cat:"no_prose" (lazy ("Suppressed by hint: " ^ id.it ^ "/" ^ (Option.get orule_id).it));
      (* NOTE: We assume the annotation of no_prose must be done in a way that, removing these rules
         and reordering them don't change the semantics of the original set of rules. This is particularly
         important if there're otherwise premises.
       *)
      false
    )
    else true
  ) clauses in
  let* clauses'' = mapiM (explicate_clause !il_env id osubid) clauses' in
  let* clauses''', if_defs = match clauses'' with
  | [] -> return ([], [])
  | _ -> select_merge_func_clauses !il_env fid clauses''
  in
  return ((id, osubid, ps, t, clauses''', opartial) $ fdef.at, if_defs)

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
