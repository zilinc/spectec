open Util
open Error
open Lib.Fun
open Lib.Option
open Source
open Il.Env
open Il.Ast
open Il.Eval
open Il.Print
open Xl.Atom
open Il2al.Def
open Il2al.Free
open Backend_ast
open Def
open Il_util


(* Errors *)

let verbose : string list ref =
  ref [ (* "inv_func"  ; *)
        (* "recover"   ; *)
        (* "rulepr"    ; *)
        (* "proj"      ; *)
        (* "uncase"    ; *)
        (* "iter"      ; *)
        (* *"iterp"    ; *)
        (* "pattern"   ; *)
        (* "log"       ; *)
        (* "case"      ; *)
        (* "knowns"    ; *)
        (* "binds"     ; *)
        (* "##binds"   ; *)
        (* "anf"       ; *)
        (* "opt"       ; *)
      ]

let error at msg = Error.error at "animation/animate" msg
let error_np msg = error no msg

let string_of_error at msg = string_of_region at ^ " IL animation error:\n" ^ msg

let warn at msg = print_endline (string_of_region at ^ " IL animation warning:\n" ^ msg)

let info v at msg = if List.mem v !verbose then
                      print_endline (string_of_region at ^ " IL animation info[" ^ v ^ "]:\n" ^ msg)
                    else
                      ()


(* Fresh name generation *)

let fresh_oracle = ref 0

let fresh_id (oname: string option) at : id =
  let i = !fresh_oracle in
  fresh_oracle := !fresh_oracle + 1;
  let name n onm = "__v" ^ string_of_int n ^
                   match onm with
                   | None -> ""
                   | Some nm -> "_" ^ nm
  in
  name i oname $ at


(* Animation monad *)



module AnimError : Lib.Error with type t = string = struct
  type t = string
  let string_of_error s = s
end


module AnimState = struct
  type t = { prems : prem list
           ; prems' : prem list
           ; knowns : Set.t
           ; progress : bool
           ; inverse : bool
           ; failure : string
           }

  let init : unit -> t = fun () ->
    { prems = []; prems' = []; knowns = Set.empty
    ; progress = false; inverse = false; failure = ""
    }

  let get_prems : t -> prem list = fun t -> t.prems
  let put_prems : prem list -> t -> t = fun ps t -> { t with prems = ps }
  let push_prem : prem -> t -> t = fun p t ->
    let ps = get_prems t in
    let ps' = p::ps in
    put_prems ps' t
  let push_prems : prem list -> t -> t = fun ps t ->
    let ps'  = get_prems t in
    let ps'' = ps @ ps' in
    put_prems ps'' t
  let pop_prem : t -> (prem * t) = fun t ->
    let ps = get_prems t in
    match ps with
    | [] -> error_np "no premise to pop from the stack."
    | p::ps' -> let t' = put_prems ps' t in (p, t')
  let peek_prem : t -> prem = fun t ->
    let ps = get_prems t in
    match ps with
    | [] -> error_np "no premise to peek from the stack."
    | p::_ -> p
  let enqueue_prem : prem -> t -> t = fun p t ->
    let ps = get_prems t in
    put_prems (ps @ [p]) t

  let get_prems' : t -> prem list = fun t -> t.prems'
  let put_prems' : prem list -> t -> t = fun ps t -> { t with prems' = ps }
  let push_prem' : prem -> t -> t = fun p t ->
    let ps = get_prems' t in
    let ps' = p::ps in
    put_prems' ps' t
  let mv_to_prems : t -> t = fun t ->
    let ps = get_prems t in
    match ps with
    | [] -> let ps' = get_prems' t in
            let t'  = put_prems' []  t  in
            let t'' = put_prems  ps' t' in
            t''
    | _ -> error_np "can't move premises to prems field, as it is not empty."

  let get_knowns : t -> Set.t = fun t -> t.knowns
  let put_knowns : Set.t -> t -> t = fun knowns t -> { t with knowns }
  let add_knowns : Set.t -> t -> t = fun knowns' t ->
    let knowns = get_knowns t in
    put_knowns (Set.union knowns knowns') t
  let remove_knowns : Set.t -> t -> t = fun knowns' t ->
    let knowns = get_knowns t in
    put_knowns (Set.diff knowns knowns') t

  let has_progress : t -> bool = fun t -> t.progress
  (* Only set progress when a premise from the primary stack gets animated
     and removed. No need to set it when more things are added to the primary
     stack, because progress is checked when we have gone through all premises
     in the primary stack. We only call this function in the main loop.
  *)
  let set_progress : t -> t = fun t -> { t with progress = true  }
  let clr_progress : t -> t = fun t -> { t with progress = false }

  let can_invert : t -> bool = fun t -> t.inverse
  let allow_inverse    : t -> t = fun t -> { t with inverse = true  }
  let disallow_inverse : t -> t = fun t -> { t with inverse = false }

  let get_failure : t -> string = fun t -> t.failure
  let set_failure : string -> t -> t = fun msg t -> { t with failure = msg }
  let clr_failure : t -> t = set_failure ""
end

module AnimateS = Lib.State(AnimState)
module AnimateE = Lib.ExceptT(AnimError)(AnimateS)

module E = AnimateE
module S = AnimateS



(* Helpers *)


(* FIXME(zilinc): I don't think it handles dependent types correctly. The binds
   should be telescopic.
*)
let binds_of_env env : bind list =
  let varbinds = Map.to_list env.vars in
  let typbinds = Map.to_list env.typs in
  let defbinds = Map.to_list env.defs in
  let grambinds = Map.to_list env.grams in
  List.map (fun (v, t)   -> ExpB (v $ no, t) $ no) varbinds
  @ List.map (fun (v, _)   -> TypB (v $ no) $ no) typbinds
  @ List.map (fun (v, def) -> (let (ps, t, _) = def in
                               DefB (v $ no, ps, t) $ no)) defbinds
  @ List.map (fun (v, def) -> (let (ps, t, _) = def in
                               GramB (v $ no, ps, t) $ no)) grambinds

let env_of_binds binds envr : Il.Env.t ref =
  List.iter (fun b -> match b.it with
    | ExpB (id, t) ->
      envr := bind_var !envr id t
    | TypB id ->
      envr := bind_typ !envr id ([], [])
    | DefB (id, ps, t) ->
      envr := bind_def !envr id (ps, t, [])
    | GramB (id, ps, t) ->
      envr := bind_gram !envr id (ps, t, [])
  ) binds;
  envr

(* Topo-sort the binding list. *)
let sort_binds id binds : bind list =
  let graph = ref [] in
  let ids = List.map (fun b -> match b.it with
    | ExpB  (id, _)    -> Il.Free.free_varid id
    | TypB   id        -> Il.Free.free_typid id
    | DefB  (id, _, _) -> Il.Free.free_defid id
    | GramB (id, _, _) -> Il.Free.free_gramid id
  ) binds in
  let bound_typ_bind b = match b.it with
  | ExpB (_, t) -> Il.Free.bound_typ t
  | _ -> empty
  in
  let vss = List.map (fun bind -> union (free_bind bind) (bound_typ_bind bind)) binds in
  List.iteri (fun i vs ->
    let deps = ref [] in
    List.iteri (fun j id -> if Il.Free.subset id vs then deps := j :: !deps) ids;
    graph := (i, !deps) :: !graph
  ) vss;
  let open Tsort in
  match sort !graph with
  | Sorted     ls -> List.map (fun idx -> List.nth binds idx) ls
  | ErrorCycle ls -> error no ("Cyclic dependency in binders: " ^ string_of_id id)


let get () = S.get () |> E.lift
let put s  = S.put s  |> E.lift
let update f = S.update f |> E.lift


type direction = [ `Lhs | `Rhs ]


(* Introduces a new binding for an expression.
   Returns the following:
    + Updated env.
    + Free variables that appear in the returned new [exp].
    + The newly created expression that binds to the argument [exp].
    + Premises for the newly introduced binding.
      - `Lhs: can also include if premises for non-linear patterns; need to animate the premises.
      - `Rhs: already animated premises.
*)
let bind_var_exp envr oname exp ot dir : Il.Env.t ref * string list * exp * prem list =
  let ( let* ) = Result.bind in
  match exp.it with
  | VarE v -> (envr, [v.it], exp, [])
  | _ ->
    let v = fresh_id oname exp.at in
    let t = match ot with Some t' -> t' | None -> exp.note in
    envr := bind_var !envr v t;
    let ve = VarE v $$ v.at % t in
    let prem_v = match dir with
    | `Lhs -> IfPr (CmpE (`EqOp, `BoolT, ve, exp) $$ exp.at % (BoolT $ exp.at)) $ exp.at
    | `Rhs -> LetPr (ve, exp, [v.it]) $ exp.at
    in
    (envr, [v.it], ve, [prem_v])

(* Instead of binding an expression to a new variable, it binds an expression
   to a *pattern*.
 *)
let bind_pat_exp envr oname exp ot dir : Il.Env.t ref * string list * exp * prem list =
  let ( let* ) = Result.bind in
  match exp.it with
  | SubE (exp', t1, t2) ->
    let (envr, vs, ve, prems_eq) = bind_var_exp envr oname exp' None dir in
    let ve' = SubE (ve, t1, t2) $> exp in
    (envr, vs, ve', prems_eq)
  | CvtE (exp', t1, t2) ->
    let (envr, vs, ve, prems_eq) = bind_var_exp envr oname exp' None dir in
    let ve' = CvtE (ve, t1, t2) $> exp in
    (envr, vs, ve', prems_eq)
  | CaseE (mixop, tup) ->
    (match tup.it with
    | TupE es ->
      let (envr, vs, ves, prems_e) = List.fold_left (fun acc e ->
        let (envr, vss, ves, premss_e) = acc in
        let (envr, vs, ve, prems_eq) = bind_var_exp envr oname e None dir in
        (envr, vss @ vs, ves @ [ve], premss_e @ prems_eq)
      ) (envr, [], [], []) es in
      let tup' = TupE ves $> tup in
      let ve' = CaseE (mixop, tup') $> exp in
      (envr, vs, ve', prems_e)
    | _ -> error exp.at ("CaseE payload is not a tuple: " ^ string_of_exp tup)
    )
  | _ -> bind_var_exp envr oname exp ot dir

let elim_lhs_known_vars envr at exp : ((string -> string) * exp * prem list) E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let pvs = (free_exp true exp).varid in
  let knowns_exp = Set.inter pvs knowns in
  if Set.is_empty knowns_exp then
    E.return (Fun.id, exp, [])
  else
    let (substs, prems_v) = List.map (fun v ->
      let v' = fresh_id (Some v) at in
      let t = find_var !envr (v $ no) in
      envr := bind_var !envr v' t;
      let ve = VarE (v $ no) $$ at % t in
      let ve' = VarE v' $$ at % t in
      let prem_v = IfPr (CmpE (`EqOp, `BoolT, ve, ve') $$ at % (BoolT $ at)) $ at in
      ((v, ve'), prem_v)
    ) (Set.to_list knowns_exp) |> Lib.List.unzip in
    let s = List.fold_left (fun s (v, e) -> Il.Subst.add_varid s (v $ no) e) Il.Subst.empty substs in
    let exp' = Il.Subst.subst_exp s exp in
    let var_subst v = if Il.Subst.mem_varid s (v $ no) |> not then v else
                        let e = Il.Subst.find_varid s (v $ no) in
                        (match e.it with | VarE v' -> v'.it | _ -> assert false)
    in
    E.return (var_subst, exp', prems_v)


(** Run animation in a new state, and return the result and the new state. *)
let run_inner (s_new: AnimState.t) (ma: 'a E.m) : ('a * AnimState.t) E.m =
  let x = S.run_state (E.run_exceptT ma) s_new in
  match x with
  | (Error e, s') -> E.throw e
  | (Ok    a, s') -> E.return (a, s')

let bracket (f_begin: AnimState.t -> AnimState.t)
            (f_end  : AnimState.t -> AnimState.t)
            (ma : 'a E.m) : 'a E.m =
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let* () = update f_begin in
  let* s' = get () in
  E.exceptT (
    let ( let* ) = S.( >>= ) in
    let* r = E.run_exceptT ma in
    match r with
    | Ok a ->
      let* () = S.update f_end in
      S.return (Ok a)
    | Error e ->
      let* () = S.put s in
      S.return (Result.Error e)
  )

let string_of_state (s: AnimState.t) =
  "prems   : length: " ^ string_of_int (List.length s.prems) ^ "\n" ^
  "prems'  : length: " ^ string_of_int (List.length s.prems') ^ "\n" ^
  "knowns  : " ^ string_of_varset s.knowns ^ "\n" ^
  "progress: " ^ string_of_bool s.progress ^ "\n" ^
  "inverse : " ^ string_of_bool s.inverse

let throw_log e = let () = info "log" no e in E.throw e

(* A list of rules/defs that cannot be easily animated.
   The map is "reason" ↦ [("rel_id", "rule_name")]
*)
let cannot_animate : (string * string) list Map.t =
  Map.of_list
    [ ("rule_lhs", [
        (* These are covered in meta.spectec. The redex is either
           FRAME_, LABEL_ or HANDLER_.
         *)
        ("Step_pure", "br-label-zero");
        ("Step_pure", "br-label-succ");
        ("Step_pure", "br-handler");
        ("Step_pure", "return-frame");
        ("Step_pure", "return-label");
        ("Step_pure", "return-handler");

        ("Step_read", "return_call_ref-label");
        ("Step_read", "return_call_ref-handler");
        ("Step_read", "return_call_ref-frame-null");
        ("Step_read", "return_call_ref-frame-addr");

        (* These are structural rules that are hard-coded into the $reduce function in meta.spectec. *)
        ("Step_pure", "trap-instrs");
        ("Step_read", "throw_ref-instrs");
        ("Step", "ctxt-instrs");
      ])
    ]

let is_unanimatable reason rule_name rel_id : bool =
  match Map.find_opt reason cannot_animate with
  | None -> false
  | Some ls -> List.exists (fun l -> l = (rel_id, rule_name)) ls

let is_step_rule rel_id : bool = rel_id = "Step"
let is_step_pure_rule rel_id : bool = rel_id = "Step_pure"
let is_step_read_rule rel_id : bool = rel_id = "Step_read"


(* Mode analysis *)
(*
v₀ is the set of input variables in the conclusions P.
For each premise Qᵢ, we construct a set vᵢ to denote the set of variables that are already known.
Assign mode to each premise, such that:
  * All variables in vᵢ₋₁ are inputs to Qᵢ;
  * All other variables in Qᵢ are outputs;
  * If the premise is another rule, then it should have the same mode as in its definition;
  * vᵢ = vᵢ₋₁ ∪ all output variables in Qᵢ;
  * Repeat this process for Qᵢ₊₁ until Qₙ.
  * By now, vₙ should include all the output variables in P.
If this is not possible, it means that it doesn't not have a consistent mode assignment.
*)

(**
  [e1] and [e2] are the two operands of the LHS binary expression.
  [op] mayn't be an associative operator.
  [t] is the type of the input operator [op].
  Returns the inverted lhs and rhs.
 *)
let invert_bin_exp at op e1 e2 (t: numtyp) rhs : (exp * exp) E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let fv_e1 = (free_exp false e1).varid in
  let fv_e2 = (free_exp false e2).varid in
  let unknowns_e1 = Set.diff fv_e1 knowns in
  let unknowns_e2 = Set.diff fv_e2 knowns in
  let* op', t' = match op with
  | `AddOp -> if Xl.Num.sub `IntT t then
                E.return (`SubOp, t)
              else
                E.return (`SubOp, `IntT)
  | `SubOp -> E.return (`AddOp, t)
  | `MulOp -> if Xl.Num.sub `NatT t then
                E.return (`DivOp, t)
              else
                E.return (`DivOp, `NatT)
  | `DivOp -> E.return (`MulOp, t)
  | `ModOp | `PowOp ->
    E.throw (string_of_error at ("Binary operator " ^ string_of_binop (op :> binop) ^ " is not invertible."))
  in
  let* lhs', rhs' = match Set.is_empty unknowns_e1, Set.is_empty unknowns_e2 with
  | true , true  -> assert false
  | true , false -> E.return (mk_cvt ~at:e2.at e2 t t', mk_cvt ~at:e1.at e1 t t')
  | false, true  -> E.return (mk_cvt ~at:e1.at e1 t t', mk_cvt ~at:e2.at e2 t t')
  | false, false -> E.throw (string_of_error at
                               ("Can't animate binary expression where both operands contain unknowns:\n" ^
                                "  ▹ op = " ^ string_of_binop (op :> binop) ^ "\n" ^
                                "  ▹ e1 = " ^ string_of_exp e1 ^ " (unknowns: " ^ string_of_varset unknowns_e1 ^ ")\n" ^
                                "  ▹ e2 = " ^ string_of_exp e2 ^ " (unknowns: " ^ string_of_varset unknowns_e2 ^ ")"))
  in
  let rhs'' = BinE (op', (t' :> optyp), mk_cvt ~at:rhs.at rhs t t', rhs') $$ rhs.at % lhs'.note in
  E.return (lhs', rhs'')


(**
  Many of the rules appearing here are not targets of animation, and we need to have
  some special handling for each of them.
  Here is a list of them from function definitions:
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:70.37-70.43)
    Eval_expr(../specification/wasm-3.0/4.4-execution.modules.spectec:170.6-170.15)
    Module_ok(../specification/wasm-3.0/4.4-execution.modules.spectec:178.6-178.15)
    Externaddr_ok(../specification/wasm-3.0/4.4-execution.modules.spectec:179.7-179.20)
    Eval_expr(../specification/wasm-3.0/4.4-execution.modules.spectec:195.7-195.16)
    Eval_expr(../specification/wasm-3.0/4.4-execution.modules.spectec:196.7-196.16)
    Expand(../specification/wasm-3.0/4.4-execution.modules.spectec:208.6-208.12)
    Val_ok(../specification/wasm-3.0/4.4-execution.modules.spectec:209.7-209.13)
  Here is a list from reduction rules:
    Ref_ok(../specification/wasm-3.0/4.3-execution.instructions.spectec:148.6-148.12)
    Reftype_sub(../specification/wasm-3.0/4.3-execution.instructions.spectec:149.6-149.17)
    Ref_ok(../specification/wasm-3.0/4.3-execution.instructions.spectec:159.6-159.12)
    Reftype_sub(../specification/wasm-3.0/4.3-execution.instructions.spectec:160.6-160.17)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:180.6-180.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:202.6-202.12)
    Ref_ok(../specification/wasm-3.0/4.3-execution.instructions.spectec:376.6-376.12)
    Reftype_sub(../specification/wasm-3.0/4.3-execution.instructions.spectec:377.6-377.17)
    Ref_ok(../specification/wasm-3.0/4.3-execution.instructions.spectec:387.6-387.12)
    Reftype_sub(../specification/wasm-3.0/4.3-execution.instructions.spectec:388.6-388.17)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:414.6-414.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:423.6-423.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:441.6-441.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:465.6-465.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:472.6-472.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:486.6-486.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:557.6-557.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:569.6-569.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:612.6-612.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:628.6-628.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:229.6-229.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:408.6-408.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:431.6-431.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:447.6-447.12)
    Expand(../specification/wasm-3.0/4.3-execution.instructions.spectec:499.6-499.12)
*)
let rec animate_rule_prem envr at id mixop exp : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let (res, fncall) = match id.it, exp.it with
  | _, TupE [lhs; rhs] when List.mem id.it Common.step_relids ->
    let fncall = CallE (id, [ExpA lhs $ lhs.at]) $$ at % rhs.note in
    (rhs, fncall)
  | "Expand", TupE [lhs; rhs] ->
    let fid = "expanddt" $ id.at in
    let fncall = CallE (fid, [ExpA lhs $ lhs.at]) $$ at % rhs.note in
    (rhs, fncall)
  | "Eval_expr", TupE [z; lhs; z'; rhs] ->
    let arg = mk_tup [z ; lhs] in
    let res = mk_tup [z'; rhs] in
    let fncall = CallE (id, [expA arg]) $$ at % res.note in
    (res, fncall)
  (* Predicate rules. *)
  | _, TupE [s; obj; typ] when List.mem id.it ["Externtype_sub"; "Val_ok"; "Externaddr_ok"] ->
    let fncall = CallE (id, [expA s; expA obj; expA typ]) $$ at % (BoolT $ at) in
    let res = boolE true in
    (fncall, res)
  (* Other rules, mostly from validation:
     * Ref_ok : (store, ref) -> reftype
     * Module_ok : module -> moduletype
     We don't allow inverting rules, so the LHS (i.e. all args except the last one)
     of a rule must be known.
  *)
  | _, TupE es when List.length es >= 2 ->
    let lhss, rhs = Lib.List.split_last es in
    let fncall = CallE (id, List.map expA lhss) $$ at % rhs.note in
    (rhs, fncall)
  | _ -> error at ("Unknown rule form: " ^ id.it ^ "(" ^ string_of_region id.at ^")")
  in
  (* Let res = $call(args) *)
  let unknowns_res    = Set.diff (free_exp false res   ).varid knowns in
  let unknowns_fncall = Set.diff (free_exp false fncall).varid knowns in
  if not (Set.is_empty unknowns_res) && Set.is_empty unknowns_fncall then
    (* When satisfying the precondition of `animate_exp_eq`. *)
    animate_exp_eq envr at res fncall
  else if Set.is_empty unknowns_res && Set.is_empty unknowns_fncall then
    (* The rule is fully known, then check. *)
    animate_if_prem envr at (CmpE (`EqOp, `BoolT, res, fncall) $$ at % (BoolT $ at))
  else
    E.throw (string_of_error at ("LHS of rule " ^ id.it ^ " has unknowns: " ^
                                 string_of_varset unknowns_fncall))

(** ASSUMES: [lhs] contains unknown vars, whereas [rhs] is fully known.
    Essentially, the LHS is pattern to match against, and RHS is the scrutinee.
    When the LHS is an irrefutable pattern, we can invert it. When LHS
    is refutable, we have to animate it to something that we can pattern match on,
    or rewrite it as an if check. For example: match ls with [x, y] -> ... and
    this can be rewritten as a length check.
*)
and animate_exp_eq envr at lhs rhs : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  info "anf" at ("lhs = " ^ string_of_exp lhs ^ "; rhs = " ^ string_of_exp rhs);
  let (envr, vs_rhs, rhs', prems_rhs) = bind_var_exp envr None rhs None `Rhs in
  let* () = update (add_knowns (Set.of_list vs_rhs)) in
  let* prems = animate_exp_eq' envr at lhs rhs' in
  E.return (prems_rhs @ prems)

and animate_exp_eq' envr at lhs rhs : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  match lhs.it with
  (* Base case: single variable assignment. *)
  | VarE v ->
    let* () = update (add_knowns (Set.singleton v.it)) in
    E.return [ LetPr (lhs, rhs, [v.it]) $ at ]
  (* Treated as atomic. *)
  (* | DotE (lhs', mixop) -> _ *)
  (* function call; invert it. *)
  | CallE (fid, args) when can_invert s ->
    let varid = fun s -> s.varid in
    let fv_args = List.map (free_arg false) args |> List.map varid in
    let unknowns = List.map (fun fv_arg -> Set.diff fv_arg knowns) fv_args in
    let oinv_fid = find_func_hint !envr fid.it "inverse" in
    let* inv_fid = match oinv_fid with
    | None ->
        info "inv_func" at ("No inverse: " ^ string_of_exp lhs ^ " = " ^ string_of_exp rhs);
        info "inv_func" at ("Knowns: " ^ string_of_varset knowns);
        E.throw (string_of_error at ("No inverse function declared for `" ^ fid.it ^ "`, so can't invert it."))
    | Some hint -> begin match hint.hintexp.it with
      | CallE (fid, []) -> E.return fid
      | _ -> E.throw (string_of_error at ("Ill-formed inverse hint for function `" ^ fid.it ^ "`, so can't invert it."))
      end in
    let _ = info "inv_func" at ("Function " ^ fid.it ^ " is being inverted") in
    (* Only the last argument is invertible. *)
    let args_hd, arg_lt = Lib.List.split_last args in
    let o_unknown_arg = List.find_opt (fun arg ->
      let fv_arg = (free_arg false arg).varid in
      Set.is_empty (Set.diff fv_arg knowns) |> not
    ) args_hd in
    begin match o_unknown_arg with
    | None ->
      (* It is implied that the last argument contains unknowns, because [lhs] contains unknowns. *)
      let args' = args_hd @ [ExpA rhs $ rhs.at] in
      begin match arg_lt.it with
      | ExpA lhs' ->
        let fncall = CallE (inv_fid, args') $$ at % lhs'.note in
        animate_exp_eq envr at lhs' fncall
      | _ ->
        E.throw (string_of_error at ("The last argument of function `" ^ fid.it ^ "` is not invertible:\n" ^
                                     "  ▹ Argument: " ^ string_of_arg arg_lt))
      end
    | Some unknown_arg ->
      let unknowns_arg = Set.diff ((free_arg false unknown_arg).varid) knowns in
      E.throw (string_of_error at ("We can only invert the last argument of function `" ^ fid.it ^ "`,\n" ^
                                   "but the following argument contains unknowns: " ^ string_of_arg unknown_arg ^ "\n" ^
                                   "  ▹ Unknowns: " ^ string_of_varset unknowns_arg))
    end
  | IterE (lhs', ((iter, xes) as iterexp)) ->
    (* To animate -- if lhs^iter = rhs:
       ~~>
       -- let N = |rhs|
       animate (depending on ^iter, check the range of N: -- if ... N ...)
       animate -- if lhs^(i<N) = rhs
       ~~>
       ...
       ...
       animate -- (if lhs = rhs[i])^(i<N)
       ~~>
       ...
       ...
       (this premise will be handled by the `animate_prem (IterPr {})` case.)
    *)
    begin match iter with
    (* Special case *)
    | Opt ->
      let (envr, vs, ve, prems_lhs) = bind_var_exp envr None lhs' None `Lhs in
      let blob = List.map (fun v ->
        (match List.find_opt (fun (x, e) -> x.it = v) xes with
        | Some (xI, eI) ->
          let v_eI = (match eI.it with
          | VarE v_eI -> v_eI
          | _ -> assert false
          ) in
          (xI, v_eI, eI)
        | None ->
          let v' = Frontend.Dim.annot_varid (v $ no) [iter] in
          let v_question = fresh_id (Some v'.it) ve.at in
          let t = find_var !envr (v $ no) in
          let t_question = IterT (t, iter) $ no in
          let ve_question = VarE v_question $$ ve.at % t_question in
          envr := bind_var !envr v_question t_question;
          (v $ no, v_question, ve_question)
        )
      ) vs in
      let xes', v_questions = Lib.List.unzip3 blob |> fun (xs, ys, zs) -> (List.combine xs zs, List.map it ys) in
      let prem_opt = LetPr (IterE (ve, (iter, xes')) $$ lhs.at % lhs'.note, rhs, v_questions) $ at in
      let* () = update (add_knowns (Set.of_list v_questions)) in
      (* [xes'] contains only the bindings in the new inner LHS, i.e. [ve], but when the new LHS is
         different from the old LHS, the bindings of the old LHS, which are stored in [xes], need to be included.
      *)
      let merge xes1 xes2 = List.fold_left (fun xes (xI, eI) ->
        if List.exists (fun (xI1, eI1) -> Il.Eq.eq_id xI1 xI) xes1 then
          xes
        else
          (xI, eI) :: xes
      ) xes1 xes2
      in
      let xes'' = merge xes' xes in
      let* prems_iter' = animate_prem envr (IterPr (prems_lhs, (iter, xes'')) $ at) in
      E.return (prem_opt :: prems_iter')
    (* Base case *)
    | ListN(len, Some i) ->
      let fv_len = (free_exp false len).varid in
      let unknowns_len = Set.diff fv_len knowns in
      if Set.is_empty unknowns_len then
        (* Base case for iterators *)
        let t = reduce_typ !envr lhs'.note in
        let rhs' = IdxE (rhs, VarE i $$ i.at % (natT ~at:i.at ())) $$ rhs.at % lhs'.note in
        let prem_body = IfPr (CmpE (`EqOp, `BoolT, lhs', rhs') $$ at % (BoolT $ at)) $ at in
        bracket (add_knowns (Set.singleton i.it))
                (remove_knowns (Set.singleton i.it))
                (animate_prem envr (IterPr ([prem_body], iterexp) $ at))
      else
        (* Inductive case where [len] is unknown. *)
        let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
        let* prem_len = animate_exp_eq envr len.at len len_rhs in
        (* By now [len] should be known. *)
        let* prems' = animate_exp_eq envr at lhs rhs in
        E.return (prem_len @ prems')
    (* Inductive cases *)
    | ListN(len, None) ->
      let i = fresh_id (Some "i") at in
      let i_star = Frontend.Dim.annot_varid i [iter] in
      let t_star = IterT (natT ~at:i_star.at (), List) $ i_star.at in
      let i_star_e = VarE i_star $$ i_star.at % t_star in
      envr := bind_var !envr i_star t_star;
      let xes' = (i, i_star_e) :: xes in
      animate_exp_eq envr at (IterE (lhs', (ListN(len, Some i), xes')) $> lhs) rhs
    | List | List1 ->
      let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
      let len_v = fresh_id (Some "len") len_rhs.at in
      envr := bind_var !envr len_v (natT ~at:len_rhs.at ());
      let len = VarE len_v $$ len_rhs.at % len_rhs.note in
      let* prems_len_v = animate_exp_eq envr len.at len len_rhs in
      let oprem_len = match iter with
      | List  -> None
      | List1 -> Some (IfPr (CmpE (`GeOp, `NatT, len, mk_nat ~at:len.at 1) $$ len.at % (BoolT $ len.at)) $ at)
      | _     -> assert false
      in
      let* prems_len = match oprem_len with
      | None -> E.return []
      | Some prem_len -> animate_prem envr prem_len
      in
      let* prems' = animate_exp_eq envr at (IterE (lhs', (ListN(len, None), xes)) $> lhs) rhs in
      E.return (prems_len_v @ prems_len @ prems')
    end
  (* AST nodes that can be inverted. *)
  | StrE expfields ->
    let prems = List.map (fun (atom, exp) ->
      let lhs' = exp in
      let rhs' = DotE (rhs, atom) $$ rhs.at % exp.note in
      IfPr (CmpE (`EqOp, `BoolT, lhs', rhs') $$ at % (BoolT $ at)) $ at
    ) expfields
    in
    let s_new = { (init ()) with prems; knowns } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return prems'
  | SubE (exp, t1, t2) ->
    let (envr, vs, ve, prems_v) = bind_var_exp envr None exp None `Lhs in
    let prem' = LetPr (SubE (ve, t1, t2) $> lhs, rhs, vs) $ at in
    let* () = update (add_knowns (Set.of_list vs)) in
    let* prems_v' = E.(mapM (animate_prem envr) prems_v <&> List.concat) in
    E.return (prem' :: prems_v')
  | OptE None -> assert false  (* Because lhs must contain unknowns *)
  | OptE (Some exp) ->
    let (envr', vs, ve, prems_v) = bind_var_exp envr None exp None `Lhs in
    let prem_opt = LetPr (OptE (Some ve) $$ lhs.at % rhs.note, rhs, vs) $ at in
    let* () = update (add_knowns (Set.of_list vs)) in
    let* prems_v' = E.(mapM (animate_prem envr) prems_v <&> List.concat) in
    E.return (prem_opt :: prems_v')
  | ListE [] ->
    assert false  (* Because lhs must contain unknowns. *)
  | ListE exps ->
    (* We need a length check to serve as the irrefutable list pattern. *)
    let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
    let len_lhs = mk_nat ~at:lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`EqOp, `BoolT, len_lhs, len_rhs) $$ at % (BoolT $ at)) $ at in
    let prems = List.mapi (fun i exp ->
          let ie = mk_nat ~at:exp.at i in
          IfPr (CmpE (`EqOp, `BoolT, exp, IdxE (rhs, ie) $$ rhs.at % exp.note)
                  $$ exp.at
                  %  (BoolT $ exp.at)
               ) $ exp.at
        ) exps in
    (* Start an inner loop, in case the list components have dependencies.inverse
       For example, if we had `[x + 1; x] = rhs`, which gets decomposed into
         -- if x + 1 = rhs.0
         -- if x = rhs.1
       If we can't animate `x + 1` (hypothetically, if it was something difficult),
       we can still solve it by first computing `x`.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems; knowns = get_knowns s' } in
    let* prems', s_new' = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return ([prem_len] @ prems')
  | CaseE (mixop, lhs') ->
    info "case" at ("The payload of constructor " ^ string_of_mixop mixop ^ " is " ^ string_of_exp lhs');
    info "case" at ("The LHS: (" ^ string_of_exp lhs ^ ") type is " ^ string_of_typ lhs.note);
    info "case" at ("The RHS: (" ^ string_of_exp rhs ^ ") type is " ^ string_of_typ rhs.note);
    begin match as_variant_typ !envr rhs.note with
    | [] -> assert false
    | [(mixop', (_, t, _), _)] when Il.Eq.eq_mixop mixop mixop' ->
      animate_exp_eq envr at lhs' (UncaseE (rhs, mixop) $$ rhs.at % lhs'.note)
      (*
      (* NOTE: Rebind the RHS to a fresh variable. This is only needed to lift
         the function call nodes to the top of the AST.
      *)
      begin match bind_var_exp envr None rhs None with
      | Error _ -> animate_exp_eq envr at lhs' (UncaseE (rhs, mixop) $$ rhs.at % lhs'.note)
      | Ok (envr, v, ve, prem_v) ->
        let* prems_v' = animate_prem envr prem_v in
        let* prems' = animate_exp_eq envr at lhs' (UncaseE (ve, mixop) $$ ve.at % lhs'.note) in
        E.return (prems_v' @ prems')
      end
      *)
    | tcases ->
      begin match lhs'.it with
      | TupE es ->
        let (_, (_bs, t', _), _) = List.find (fun (mixop', _, _) -> Il.Eq.eq_mixop mixop mixop') tcases in
        let ets = as_tup_typ !envr t' in
        let (envr, vs, ves, prem_vs) = List.fold_left (fun acc (e, (_, t)) ->
          let (envr, vs, ves, prem_vs) = acc in
          (* NOTE: If we use `t` to type the new variable below, then it's possible that some of them
             do not reduce, and will cause later pattern matching on the types to fail.
          *)
          let (envr', vs', ve, prems_v) = bind_var_exp envr None e None `Lhs in
          (envr', vs @ vs', ves@[ve], prem_vs @ prems_v)
        ) (envr, [], [], []) (List.combine es ets) in
        let tup = TupE ves $$ lhs.at % lhs.note in
        let* (subst_vs, tup', prems_ves) = elim_lhs_known_vars envr tup.at tup in
        let vs' = List.map subst_vs vs in
        let prem_case = LetPr (CaseE (mixop, tup') $$ lhs.at % rhs.note, rhs, vs') $ at in
        info "case" at ("CaseE-TupE prem_vs: " ^ String.concat "\n" (List.map string_of_prem prem_vs));
        let* () = update (add_knowns (Set.of_list vs')) in
        (* FIXME(zilinc): It may not handle patterns like C(v, v, v) correctly. *)
        let* s' = get () in
        let s_new = { (init ()) with prems = prem_vs @ prems_ves; knowns = get_knowns s' } in
        let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
        let* () = update (put_knowns (get_knowns s_new')) in
        E.return (prem_case :: prems')
      | _ ->
        assert false
        (*
        (* Use tcases to work out the type of ve, because it retains the dependent tuple type. *)
        let (_, (bs, t', _), _) = List.find (fun (mixop', _, _) -> Il.Eq.eq_mixop mixop mixop') tcases in
        info "case" no ("lhs'.note = " ^ string_of_typ lhs'.note);
        info "case" no ("t' from rhs = " ^ string_of_typ t');
        begin match bind_var_exp envr None lhs' (Some t') with
        | Ok (envr, v, ve, prem_v) ->
          let envr = env_of_binds bs envr in
          let prem_case = LetPr (CaseE (mixop, ve) $$ lhs.at % rhs.note, rhs, [v.it]) $ at in
          let* () = update (add_knowns (Set.singleton v.it)) in
          let* prems' = animate_prem envr prem_v in
          E.return (prem_case :: prems')
        | Error v ->
          let* () = update (add_knowns (Set.singleton v.it)) in
          E.return [LetPr (lhs, rhs, [v.it]) $ at]
        end
        *)
      end
    end
  | TupE es ->
    (* simp *)
    let prems = Fun.flip List.mapi es (fun i e ->
      let bool_t = BoolT $ e.at in
      let proj_rhs = ProjE (rhs, i) $$ rhs.at % e.note in
      info "case" rhs.at ("Proj " ^ string_of_exp proj_rhs ^ "'s type is " ^ string_of_typ e.note);
      info "case" rhs.at ("RHS " ^ string_of_exp rhs ^ "'s type is " ^ string_of_typ rhs.note);
      IfPr (CmpE (`EqOp, `BoolT, e, proj_rhs) $$ e.at % bool_t) $ at)
    in
    (* Need to animate the components in a loop. This is needed
       if we have premises like `(... x ..., x) = (e1, e2)`, where the first
       component cannot be animated when `x` is unknown. By solving the second
       first, we turn the first into a check.
    *)
    let* () = update (push_prems prems) in
    E.return []
  | CvtE (lhs', t1, t2) ->
    (* TODO(zilinc): Conversion is not checked. *)
    animate_exp_eq envr at lhs' (CvtE (rhs, t2, t1) $$ rhs.at % lhs'.note)
  (* Some operators, together with certain combinations of a known operand plus
     the known RHS, can be inverted.
  *)
  | BinE ((#Xl.Num.binop as op), (#Xl.Num.typ as t), e1, e2) ->
    let* lhs', rhs' = invert_bin_exp at op e1 e2 t rhs in
    animate_exp_eq envr at lhs' rhs'
  | BinE ((#Xl.Bool.binop as op), (#Xl.Bool.typ as t), e1, e2) ->
    E.throw (string_of_error at ("Boolean binary operators not animated."))
  (* All unary ops can be inverted. *)
  | UnE (op, t, exp) ->
    animate_exp_eq envr at exp (UnE (op, t, rhs) $$ rhs.at % exp.note)
  (* Unary tuples. Invert. *)
  | ProjE (e1, 0) ->
    let t' = reduce_typ !envr e1.note in
    begin match t'.it with
    | VarT _ -> assert false
    | TupT [_] ->
      info "proj" at ("ProjE.0 on an ordinary singleton TupT type.");
      animate_exp_eq envr at e1 (TupE [rhs] $$ rhs.at % e1.note)
    | NumT _ ->
      (* It is possible that both e1.0 and e1 have the same type. *)
      info "proj" at ("Num type: " ^ string_of_typ t');
      animate_exp_eq envr at e1 (TupE [rhs] $$ rhs.at % e1.note)
    | _ -> E.throw (string_of_error at
                     ("Can't invert ProjE.0: " ^ string_of_exp e1 ^ " of type " ^ string_of_typ t'))
    end
  (* Unary constructors. Invert. *)
  | UncaseE (e1, mixop) ->
    (* Technically, need to check for the refinement when wrapping with a CaseE. *)
    begin match as_variant_typ !envr e1.note with
    (* Unary variant type, we can invert the UncaseE. *)
    | [(mixop', (_, _t, _), _)] when Il.Eq.eq_mixop mixop mixop' ->
      animate_exp_eq envr at e1 (CaseE (mixop, rhs) $$ rhs.at % e1.note)
      (*
      (* TODO(zilinc): The side-condition from the type definition.
         For now, we don't check it. But the check can be added in a separate
         phase that follows animation.
       *)
      let (mixop', (binds, t', prems), hints) = tc in
      if mixop = mixop' then
        let () = info "uncase" at ("invert CaseE on " ^ string_of_mixop mixop) in
        if List.is_empty prems then
          animate_exp_eq at e1 (CaseE (mixop, rhs) $$ rhs.at % e1.note)
        else
          (* Animate the cast dynamic checks in a new state. *)
          let at'  = over_region (List.map Source.at prems) in
          let ins' = (bound_binds binds).varid in
          let ous' = (free_binds  binds).varid in
          let prems' = animate_prems at' ins' ous' prems in
          (* The output vars from the above is totally separate to the main animation,
             as they are from the type definition. therefore there's no need to update
             the knowns in the state.
          *)
          let* prems'' = animate_exp_eq at e1 (CaseE (mixop, rhs) $$ rhs.at % e1.note) in
          E.return (prems' @ prems'')
      else
        assert false
      *)
    | _ -> assert false
    end
  (* More complicated patterns that are partially invertible. *)
  (* [e1; e2; ...; en] ++ exp2 *)
  | CatE (({ it = ListE exps; _ } as exp1), exp2) ->
    let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
    let (envr, vs_len_rhs, len_rhs', prems_v_len_rhs) = bind_var_exp envr None len_rhs None `Rhs in
    let* () = update (add_knowns (Set.of_list vs_len_rhs)) in
    let len_lhs1 = mk_nat ~at:lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`LeOp, `NatT, len_lhs1, len_rhs') $$ len_rhs'.at % (BoolT $ len_rhs'.at)) $ len_rhs'.at in
    let prems1 = List.mapi (fun i exp ->
      let idx = NumE (`Nat (Z.of_int i)) $$ exp.at % (natT ~at:exp.at ()) in
      let rhs' = IdxE (rhs, idx) $$ exp.at % exp.note in
      IfPr (CmpE (`EqOp, `BoolT, exp, rhs') $$ exp.at % (BoolT $ exp.at)) $ at
    ) exps in
    let start2 = len_lhs1 in
    let len_lhs2 = mk_cvt_sub ~at:exp2.at len_rhs' len_lhs1 in
    let rhs2' = SliceE (rhs, start2, len_lhs2) $$ rhs.at % rhs.note in
    let prem2 = IfPr (CmpE (`EqOp, `BoolT, exp2, rhs2') $$ exp2.at % (BoolT $ exp2.at)) $ at in
    (* Start an inner loop, in case of any dependencies between the list elements.
       E.g. -- if [v, v] v'* = rhs
       The first [v] is a binding, and the second becomes a check.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems = prems1 @ [prem2]; knowns = get_knowns s' } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prems_v_len_rhs @ prem_len :: prems')
  (* exp1 ++ [e1; e2; ...; en] *)
  | CatE (exp1, ({ it = ListE exps; _ } as exp2)) ->
    let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
    let (envr, vs_len_rhs, len_rhs', prems_v_len_rhs) = bind_var_exp envr None len_rhs None `Rhs in
    let* () = update (add_knowns (Set.of_list vs_len_rhs)) in
    let len_lhs2 = mk_nat ~at:lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`LeOp, `NatT, len_lhs2, len_rhs') $$ len_rhs'.at % (BoolT $ len_rhs'.at)) $ len_rhs'.at in
    let prems2 = List.mapi (fun i exp ->
      let idx = NumE (`Nat (Z.of_int i)) $$ exp.at % (natT ~at:exp.at ()) in
      (* idx' = len - (len2 - idx) *)
      let idx' = mk_cvt_sub ~at:len_lhs2.at len_rhs' (mk_cvt_sub ~at:len_lhs2.at len_lhs2 idx) in
      let rhs' = IdxE (rhs, idx') $$ exp.at % exp.note in
      IfPr (CmpE (`EqOp, `BoolT, exp, rhs') $$ exp.at % (BoolT $ exp.at)) $ at
    ) exps in
    let start1 = mk_nat 0 in
    let len_lhs1 = mk_cvt_sub ~at:exp1.at len_rhs' len_lhs2 in
    let rhs1' = SliceE (rhs, start1, len_lhs1) $$ rhs.at % rhs.note in
    let prem1 = IfPr (CmpE (`EqOp, `BoolT, exp1, rhs1') $$ exp1.at % (BoolT $ exp1.at)) $ at in
    (* Start an inner loop, in case of any dependencies between the list elements.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems = prems2 @ [prem1]; knowns = get_knowns s' } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prems_v_len_rhs @ prem_len :: prems')
  (* exp1 ++ exp2'^n where n is known *)
  | CatE (exp1, ({ it = IterE (exp2', (ListN(len_lhs2, _), xes)); _} as exp2))
    when Set.subset ((free_exp false len_lhs2).varid) knowns ->
    let len_rhs = LenE rhs $$ rhs.at % (natT ~at:rhs.at ()) in
    let (envr, vs_len_rhs, len_rhs', prems_v_len_rhs) = bind_var_exp envr None len_rhs None `Rhs in
    let* () = update (add_knowns (Set.of_list vs_len_rhs)) in
    let prem_len = IfPr (CmpE (`LeOp, `NatT, len_lhs2, len_rhs') $$ len_rhs'.at % (BoolT $ len_rhs'.at)) $ len_rhs'.at in
    let start1 = mk_nat 0 in
    let len_lhs1 = mk_cvt_sub ~at:exp1.at len_rhs' len_lhs2 in
    let rhs1' = SliceE (rhs, start1, len_lhs1) $> rhs in
    let rhs2' = SliceE (rhs, len_lhs1, len_lhs2) $> rhs in
    let prem1 = IfPr (eqE ~at:exp1.at exp1 rhs1') $ at in
    let prem2 = IfPr (eqE ~at:exp2.at exp2 rhs2') $ at in
    (* Start an inner loop, in case of any dependencies between the list elements.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems = [prem1; prem2]; knowns = get_knowns s' } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prems_v_len_rhs @ prem_len :: prems')
  (* exp1* ++ [X] ++ exp2* *)
  (*
  | CatE ({ it = CatE ({ it = IterE (exp1', (List, xes1)); _ },
                       { it = ListE [{ it = CaseE _; _ }]; _ })
          ; _ },
          { it = IterE (exp2', (List, xes2)); _ }) ->
    todo "maybe better off just handle the rules manually."
  *)
  | _ -> E.throw (string_of_error at ("Can't pattern match or compute LHS: " ^ string_of_exp lhs))


(** ASSUMES: [e] contains unknown vars, whereas [es] is fully known.
    ENSURES: When it returns Error, it means that the original premise should be
    used as the animated premise.
 *)
and animate_exp_mem envr at e es : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let (envr, vs, e', prems_v) = bind_pat_exp envr None e None `Lhs in
  let (envr, vs', es', prems_es) = bind_var_exp envr None es None `Rhs in
  let* () = update (add_knowns (Set.of_list vs')) in
  let prem_len_es = IfPr (gtE ~at:at (lenE ~at:(es'.at) es') (natE ~at:at Z.zero)) $ at in
  let zero = NumE (`Nat Z.zero) $$ e'.at % (natT ~at:e'.at ()) in
  let es_0 = IdxE (es', zero) $$ es'.at % e'.note in
  let* () = update (add_knowns (Set.of_list vs)) in
  let prem' = LetPr (e', es_0, vs) $ at in
  let* prems_v' = E.(mapM (animate_prem envr) prems_v <&> List.concat) in
  E.return (prems_es @ [prem_len_es; prem'] @ prems_v')

and animate_if_prem envr at exp : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let fv_exp = (free_exp false exp).varid in
  let* s = get () in
  let knowns = get_knowns s in
  match exp.it with
  (* Base case: all free vars are inputs *)
  | _ when Set.subset fv_exp knowns ->
    E.return [ IfPr exp $ at ]
  (* lhs = rhs *)
  | CmpE (`EqOp, t, e1, e2) ->
    let fv1 = (free_exp false e1).varid in
    let fv2 = (free_exp false e2).varid in
    let unknowns1 = Set.diff fv1 knowns in
    let unknowns2 = Set.diff fv2 knowns in
    (match Set.is_empty unknowns1, Set.is_empty unknowns2 with
    | true , true  -> assert false
    | true , false -> animate_exp_eq envr exp.at e2 e1
    | false, true  -> animate_exp_eq envr exp.at e1 e2
    | false, false -> E.throw (string_of_error at (
                                 "e1 = e2 where both sides have unknowns.\n" ^
                                 "  ▹ e1 = " ^ string_of_exp e1 ^ "\n" ^
                                 "    unknowns: " ^ string_of_varset unknowns1 ^ "\n" ^
                                 "  ▹ e2 = " ^ string_of_exp e2 ^ "\n" ^
                                 "    unknowns: " ^ string_of_varset unknowns2))
  )
  (* simp: Break up conjunctions. We have to push the two conjuncts on the stack
     and hand over the control to the outer loops, because these two conjuncts
     may need to be animated in different iterations.
   *)
  | BinE (`AndOp, _, e1, e2) ->
    (* This should be the few places where we manipulate the stack, because the conjuncts
       are totally independent of each other and can be flattened into the main loop.
     *)
    let* () = update (push_prems [IfPr e2 $ e2.at; IfPr e1 $ e1.at]) in
    E.return []
  (* Membership or nondeterministic choice: e1 ∈ e2 *)
  | MemE (e1, e2) ->
    let fv1 = (free_exp false e1).varid in
    let fv2 = (free_exp false e2).varid in
    let unknowns1 = Set.diff fv1 knowns in
    let unknowns2 = Set.diff fv2 knowns in
    (match Set.is_empty unknowns1, Set.is_empty unknowns2 with
    | true , true  -> assert false
    | true , false -> E.throw (string_of_error at (
                                "e2 in e1 ∈ e2 contains unknowns.\n" ^
                                "  ▹ e2 = " ^ string_of_exp e2))
    | false, true  -> animate_exp_mem envr exp.at e1 e2
    | false, false -> E.throw (string_of_error at (
                                 "e1 ∈ e2 where both sides have unknowns.\n" ^
                                 "  ▹ e1 = " ^ string_of_exp e1 ^ "\n" ^
                                 "  ▹ e2 = " ^ string_of_exp e2))
    )
  | IterE (exp', iterexp) ->
    animate_prem envr (IterPr ([IfPr exp' $ exp'.at], iterexp) $ at)
  | _ -> let unknowns = Set.diff fv_exp knowns in
         E.throw (string_of_error at (
                   "Can't animate if premise: " ^ string_of_exp exp ^ ".\n" ^
                   "  ▹ Unknowns: " ^ string_of_varset unknowns ^ "\n" ^
                   "  ▹ Knowns: " ^ string_of_varset knowns))


and animate_prem envr prem : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let fv_prem = (free_prem false prem).varid in
  match prem.it with
  | RulePr (id, mixop, exp) ->
    info "rulepr" prem.at ("rule premise: " ^ id.it);
    animate_rule_prem envr prem.at id mixop exp
  | IfPr exp -> animate_if_prem envr prem.at exp
  | LetPr (e1, e2, ids) ->
    error prem.at ("Can't animate LetPr: " ^ string_of_prem prem)
  | ElsePr ->
    E.return [ prem ]
  | IterPr ([], _) -> E.return []
  | IterPr (prems, ((List|List1) as iter, xes)) ->
    (* Reduce them to ListN(_, None). *)
    let list_e = List.find_map (fun (x, e) ->
      let fv_e = (free_exp false e).varid in
      if Set.subset fv_e knowns then Some e else None
    ) xes |> Option.get in
    let len_v = fresh_id (Some "len") list_e.at in
    envr := bind_var !envr len_v (natT ());
    let len_e = VarE len_v $$ len_v.at % (natT ()) in
    let prem_len = LetPr (len_e, LenE list_e $> len_e, [len_v.it]) $ prem.at in
    let* () = update (add_knowns (Set.singleton len_v.it)) in
    let prem_list1 = match iter with 
    | List  -> []
    | List1 -> [IfPr (CmpE(`GeOp, `NatT, len_e, mk_nat 1) $$ len_e.at % (BoolT $ len_e.at)) $ prem.at]
    | _ -> assert false
    in
    let prem' = IterPr (prems, (ListN(len_e, None), xes)) $ prem.at in
    let* prems' = animate_prem envr prem' in
    E.return (prem_len :: prem_list1 @ prems')
  | IterPr (prems, (ListN(len, None) as iter, xes)) ->
    (* Reduce them to ListN(_, Some _). *)
    let i = fresh_id (Some "i") len.at in
    let i_star = Frontend.Dim.annot_varid i [iter] in
    let t_star = IterT (natT ~at:i_star.at (), List) $ i_star.at in
    let i_star_e = VarE i_star $$ i_star.at % t_star in
    envr := bind_var !envr i_star t_star;
    let xes' = (i, i_star_e) :: xes in
    let prem' = IterPr (prems, (ListN(len, Some i), xes')) $ prem.at in
    animate_prem envr prem'
  | IterPr (prems, (((Opt|ListN(_, Some _)) as iter, xes) as iterexp)) ->
    let lenvr = ref !envr in
    (* Propagating knowns into the iteration. *)
    let oindex = match iter with
    | ListN(len, Some i) ->
      lenvr := bind_var !lenvr i (natT ~at:len.at ());
      let fv_len = (free_exp false len).varid in
      if Set.is_empty (Set.diff fv_len knowns) then
        Some i
      else
        (* It should have been caught by the IL validator. *)
        assert false
    | _ -> None
    in
    (* The new bindings that are introduced by the iteration. *)
    let knowns_iter = List.filter_map (fun (x, e) ->
      let fv_e = (free_exp false e).varid in
      let unknowns_e = Set.diff fv_e knowns in
      if Set.is_empty unknowns_e then Some x.it else None
    ) xes |> Set.of_list in
    let knowns_inner = Set.union knowns knowns_iter in
    let knowns_inner_idx = match oindex with
    | None   -> knowns_inner
    | Some i -> Set.add i.it knowns_inner in
    let s_body = { (init ()) with prems; knowns = knowns_inner_idx } in
    let* (prems_body', s_body') = run_inner s_body (animate_prems' lenvr prem.at) in
    let new_knowns = Set.diff (get_knowns s_body') (get_knowns s_body) in
    (* Add the static variables that need to flow out but are not in the binding list.
       Intermediate variables are excluded.
       NOTE the side effect of updating [envr].
    *)
    let xes' = List.concat_map (fun x ->
      if String.starts_with ~prefix:"__v" x || List.exists (fun (x', _) -> x'.it = x) xes
      then
        (info "binds" prem.at ("Variable `" ^ x ^ "` is intermediate or is in binding list"); [])
      else
        (* Not in the binding list and not intermediate variables *)
        let x_star = Frontend.Dim.annot_varid (x $ no) [iter] in
        let t = find_var !lenvr (x $ no) in
        let iter' = match iter with Opt -> Opt | _ -> List in
        let t_star = IterT (t, iter') $ x_star.at in
        envr := bind_var !envr x_star t_star;
        info "binds" prem.at ("Add " ^ x_star.it ^ " to type binding");
        [(x $ x_star.at, VarE x_star $$ x_star.at % t_star)]
    ) (Set.to_list new_knowns) in
    (* Propagate the new binders (type-binding) from the inner premises to the outside. *)
    List.iter (fun (v, t) ->
      if List.exists (fun (x', _) -> x'.it = v) xes then
        info "##binds" prem.at ("## Variable " ^ v ^ " in binding list")
      else
        (* For those who don't bind to a higher dim variable, add them to the
           top-level type binds. A variable is either bound at the top level,
           or via the iterator binding list [xes].
        *)
        let t = find_var !lenvr (v $ no) in
        info "##binds" prem.at ("## Add " ^ v ^ " to type binding");
        envr := bind_var !envr  (v $ no) t
    ) ((Il.Env.env_diff !lenvr !envr).vars |> Il.Env.Map.to_list);
    (* Propagate knowns to the outside of the iterator. We traverse [xes] and [xes'],
       because they together include all the variables that need to flow out.
       But the entries in [xes] and in [xes'] generate different premises.
    *)
    let blob1 = List.map (fun (x, e) ->
      begin match e.it with
      | VarE v -> ([v.it], [])
      | _ ->
        (* If [e] is not a single variable and it's out-flowing in {x <- e},
           then we create a fresh [v], such that {x <- v}, and -- if v = e
           after we finish the interation.
        *)
        let x' = Frontend.Dim.annot_varid x [iter] in
        let x_star = fresh_id (Some x'.it) e.at in
        envr := bind_var !envr x_star e.note;
        let x_star_e = VarE x_star $$ e.at % e.note in
        let prem_e = IfPr (CmpE (`EqOp, `BoolT, e, x_star_e) $$ e.at % (BoolT $ e.at)) $ e.at in
        ([x_star.it], [prem_e])
      end
    ) xes
    in
    let blob2 = List.map (fun (x, e) ->
      (* If there's no x <- e, then propagate x out. This can happen if there's a
         -- where x = ... inside the iterator. That `x` needs to be transfered to the
         outer scope. But we also need to avoid doing so for any intermediate variables
         that are genuinely only visible inside.
         If we have ( -- where a = rhs )^iter { ... } and a is not in the binding list,
         then we generate the following DL:
           ( -- where __v = ...
             -- where a = ...
           )^iter { ... , a <- a* }
           -- if |a*| > 0
           -- where a = a*[0]
           (-- if a = a*[i])^(i < |a*|)
      *)
      let VarE x_star = e.it in
      let len = LenE e $$ e.at % (natT ~at:e.at ()) in
      let prem_len = IfPr (CmpE (`GeOp, `NatT, len, mk_nat 0) $$ len.at % (BoolT $ len.at)) $ len.at in
      let t = find_var !lenvr x in
      let x0 = IdxE (e, mk_nat 0) $$ e.at % t in
      let xe = VarE x $$ x.at % t in
      envr := bind_var !envr x t;
      let prem_x0 = LetPr (xe, x0, [x.it]) $ e.at in
      let i = fresh_id (Some "i") len.at in
      let iter = ListN (len, Some i) in
      let e_i = IdxE (e, VarE i $$ i.at % (natT ~at:i.at ())) $$ e.at % x0.note in
      let prem_eq = IfPr (CmpE (`EqOp, `NatT, xe, e_i) $$ xe.at % (BoolT $ xe.at)) $ xe.at in
      let prem_eq_iter = IterPr ([prem_eq], (iter, [])) $ xe.at in
      ([x.it; x_star.it], [prem_len; prem_x0; prem_eq_iter])
    ) xes'
    in
    let knowns_outer1, e_prems1 = Lib.List.unzip blob1 |> Lib.Fun.(<***>) List.concat List.concat in
    let knowns_outer2, e_prems2 = Lib.List.unzip blob2 |> Lib.Fun.(<***>) List.concat List.concat in
    let* () = update (add_knowns (Set.of_list (knowns_outer1 @ knowns_outer2))) in
    let* s_outer = get () in
    let s_end = { (init ()) with prems = e_prems1; knowns = get_knowns s_outer } in
    let* (e_prems1', s_end') = run_inner s_end (animate_prems' envr prem.at) in
    let* () = update (put_knowns (get_knowns s_end')) in
    E.return ((IterPr (prems_body', (iter, xes @ xes')) $ prem.at) :: e_prems1' @ e_prems2)
  | _ -> error prem.at ("Unable to animate premise: " ^ string_of_prem prem)


(* The main loop. We handle the ordering of the premises in this function. *)
and animate_prems' envr at : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  match (get_prems s, get_prems' s) with
  (* done with everything *)
  | ([], []) -> E.return []
  (* finished one iteration *)
  | ([], ps') -> begin match (has_progress s, can_invert s) with
    (* already allowing making inverses but still doesn't make progress *)
    | false, true ->
      let err = get_failure s in
      E.throw (string_of_error at
                 ("Can't animate the remaining premises:\n" ^
                  String.concat "\n" (List.map string_of_prem ps') ^ "\n" ^
                  "This is caused by: \n" ^
                  err))
    (* failed to make progress, but we can try allowing inverses *)
    | false, false ->
      let* () = update (allow_inverse >>> clr_progress >>> mv_to_prems) in
      animate_prems' envr at
    (* has made some progress, enter next iteration *)
    | true, _ ->
      let* () = update (clr_progress >>> mv_to_prems) in
      animate_prems' envr at
    end
  (* continue with the current iteration *)
  | _ -> let ( let* ) = S.( >>= ) in
         E.exceptT (
           let* s = S.get () in
           let (prem, s') = pop_prem s in
           let* () = S.put s' in
           let* r = animate_prem envr prem |> E.run_exceptT in
           match r with
           | Error e ->
             (* Recover from failure. NOTE: Need to also restore old known set. *)
             let* () = S.update (push_prem' prem >>> set_failure e >>> put_knowns (get_knowns s')) in
             animate_prems' envr at |> E.run_exceptT
           | Ok prems -> E.run_exceptT (
               let ( let* ) = E.( >>= ) in
               let* () = update set_progress in
               let* prems' = animate_prems' envr at in
               E.return (prems @ prems')
             )
         )

(** The top-level animation function on premises.
    [ins] is the set of known variables that are provided by the input
    of the function/rule being animated. For the first premise, it can
    only use a subset of these known variables to compute more unknowns.
    [ous] is the set of variables that need to be known by the end of
    animating all the premises, and they will be used as the output
    of the function/rule being animated. It means that [ous] must be a
    subset of all the variables that are known at the end of animating
    all the premises.
*)
and animate_prems envr at ins ous prems : prem list =
  animate_prems' envr at
  |> E.run_exceptT
  |> Fun.flip S.run_state ({ (AnimState.init ()) with prems; knowns = ins })
  |> function
     | (Error e, _) -> error at e
     | (Ok ps  , s) ->
       if Set.subset ous s.knowns then ps
       else error at ("Premises failed to compute all required output variables:\n" ^
                      "  ▹ result:\n      " ^ (String.concat "\n      " (List.map string_of_prem ps)) ^ "\n" ^
                      "  ▹ ins: " ^ string_of_varset ins ^ "\n" ^
                      "  ▹ knowns: " ^ string_of_varset s.knowns ^ "\n" ^
                      "  ▹ outs: " ^ string_of_varset ous)

let lift_otherwise_prem prems =
  let is_otherwise = function { it = ElsePr; _ } -> true | _ -> false in
  let (ow_pr, rest) = List.partition is_otherwise prems in
  ow_pr @ rest

let animate_clause_no_arg id envr (c: clause) : func_clause =
  let lenvr = ref !envr in
  let DefD (binds, args, exp, prems) = c.it in
  let lenvr = env_of_binds binds lenvr in
  let ins = (free_list (free_arg false) args).varid in
  let ous = (free_exp false exp).varid in
  let prems' = animate_prems lenvr c.at ins ous prems |> lift_otherwise_prem in
  let binds' = binds_of_env (Il.Env.env_diff !lenvr !envr) in
  let binds'' = sort_binds id binds' in
  (DefD (binds'', args, exp, prems')) $ c.at

let animate_clause id envr (c: clause) : func_clause =
  let lenvr = ref !envr in
  let DefD (binds, args, exp, prems) = c.it in
  let lenvr = env_of_binds binds lenvr in
  let n_args = List.length args in
  let (vss, args', prems_args) = List.mapi (fun i arg -> match arg.it with
    | ExpA exp' ->
      let (lenvr, vs, ve, prems_v) = bind_pat_exp lenvr (Some ("a" ^ string_of_int i)) exp' None `Lhs in
      (vs, ExpA ve $> arg, prems_v)
    | _ -> ([], arg, [])
  ) args |> Lib.List.unzip3
  in
  let ins = List.concat vss |> Set.of_list in
  let ous = (free_exp false exp).varid in
  let prems' = animate_prems lenvr c.at ins ous (List.concat prems_args @ prems) |> lift_otherwise_prem in
  let binds' = binds_of_env (Il.Env.env_diff !lenvr !envr) in
  let binds'' = sort_binds id binds' in
  (DefD (binds'', args', exp, prems')) $ c.at


(* The variant that doesn't try to animate the [lhs] of the rule, as we know that
   it's very difficult.
*)
let animate_rule_red_no_arg envr rule : func_clause =
  let (id, binds, lhs, rhs, prems) = rule.it in
  let clause = DefD (binds, [ExpA lhs $ lhs.at], rhs, prems) $ rule.at in
  animate_clause_no_arg id envr clause

let animate_rule_red envr rule : func_clause =
  let (id, binds, lhs, rhs, prems) = rule.it in
  let clause = DefD (binds, [ExpA lhs $ lhs.at], rhs, prems) $ rule.at in
  animate_clause id envr clause


(* Many $Step rules are dependent in their arguments. For example,
  ```
  rule Step_read/block:
    z; val^m ( BLOCK bt instr* )  ~>  ( LABEL_ n `{eps} val^m instr* )
    -- if $blocktype_(z, bt) = t_1^m -> t_2^n
  ```
  `m` is initially unknown, and we need to use the second part of the pattern
  `( BLOCK bt instr* )` and the premise to compute `m` and then to determine
  what values this pattern can match. This violates the precondition that all
  variables in the input (or LHS of a rule) are known.
  This transformation eliminates this circularity:
  ```
  rule Step_read/block:
    z; val* ( BLOCK bt instr* )  ~>  rest* ( LABEL_ n `{eps} val^m instr* )
    -- if $blocktype_(z, bt) = t_1^m -> t_2^n
    -- if rest* val^m = val*
  ```
  so that we can match the first part of the argument unconditionally and then
  compute `m` in the premises.
 *)

let transform_step_vals envr in_stack out_stack prems : bind list * exp * exp * prem list =
  match in_stack.it with
  | CatE ({ it = IterE (vals, (ListN(n, _), xes)); _ } as in_vals, in_stack2) ->
    let iter' = List in
    let val_ = fresh_id (Some "val") vals.at in
    let val_e = VarE val_ $$ vals.at % (t_var "val") in
    let val_e' = SubE (val_e, t_var "val", t_var "instr") $$ vals.at % t_var "instr" in
    let val_star = Frontend.Dim.annot_varid val_ [iter'] in
    let val_star_e = IterE (val_e', (iter', [(val_, VarE val_star $$ vals.at % t_star "val")])) $> vals in
    let rest = fresh_id (Some "rest") vals.at in
    let rest_e = VarE rest $> val_e in
    let rest_e' = SubE (rest_e, t_var "val", t_var "instr") $> val_e' in
    let rest_star = Frontend.Dim.annot_varid rest [iter'] in
    let rest_star_e = IterE (rest_e', (iter', [(rest, VarE rest_star $$ vals.at % t_star "val")])) $> vals in
    let in_vals' = val_star_e in
    let in_stack' = CatE (in_vals', in_stack2) $> in_stack in
    let out_stack' = CatE (rest_star_e, out_stack) $> out_stack in
    let prems' = (IfPr (eqE ~at:rest_star_e.at in_vals' (CatE (rest_star_e, in_vals) $> in_vals)) $ rest_star_e.at) :: prems in
    ([ExpB (rest_star, t_star "val") $ rest_star_e.at;
      ExpB (val_star, t_star "val") $ val_star_e.at],
     in_stack', out_stack', prems')
  (* In this case, the LHS pattern is not circular dependent as the above case, but we still
     generalise it so that we can pass in the entire value stack, instead of manually pick a
     certain number of operands to feed to the instruction.
  *)
  | ListE instrs ->
    let iter' = List in
    let rest = fresh_id (Some "rest") in_stack.at in
    let rest_e = VarE rest $$ in_stack.at % (t_var "val") in
    let rest_e' = SubE (rest_e, t_var "val", t_var "instr") $> in_stack in
    let rest_star = Frontend.Dim.annot_varid rest [iter'] in
    let rest_star_e = IterE (rest_e', (iter', [(rest, VarE rest_star $$ in_stack.at % t_star "val")])) $> in_stack in
    let in_stack' = CatE (rest_star_e, in_stack) $> in_stack in
    let out_stack' = CatE (rest_star_e, out_stack) $> out_stack in
    ([ExpB (rest_star, t_star "val") $ rest_star_e.at], in_stack', out_stack', prems)
  | _ -> [], in_stack, out_stack, prems

let transform_step_rule envr (r: rule_clause) : func_clause =
  let (rule_id, binds, lhs, rhs, prems) = r.it in
  let CaseE (in_mixop, in_tup) = lhs.it in
  let TupE [in_z; in_stack] = in_tup.it in
  let CaseE (out_mixop, out_tup) = rhs.it in
  let TupE [out_z; out_stack] = out_tup.it in
  let binds', in_stack', out_stack', prems' = transform_step_vals envr in_stack out_stack prems in
  let in_tup' = TupE [in_z; in_stack'] $> in_tup in
  let lhs' = CaseE (in_mixop, in_tup') $> lhs in
  let out_tup' = TupE [out_z; out_stack'] $> out_tup in
  let rhs' = CaseE (out_mixop, out_tup') $> rhs in
  animate_rule_red envr ((rule_id, binds @ binds', lhs', rhs', prems') $> r)

let transform_step_pure_rule envr (r: rule_clause) : func_clause =
  let (rule_id, binds, in_stack, out_stack, prems) = r.it in
  let binds', in_stack', out_stack', prems' = transform_step_vals envr in_stack out_stack prems in
  animate_rule_red envr ((rule_id, binds @ binds', in_stack', out_stack', prems') $> r)

let transform_step_read_rule envr (r: rule_clause) : func_clause =
  let (rule_id, binds, lhs, out_stack, prems) = r.it in
  let CaseE (in_mixop, in_tup) = lhs.it in
  let TupE [in_z; in_stack] = in_tup.it in
  let binds', in_stack', out_stack', prems' = transform_step_vals envr in_stack out_stack prems in
  let in_tup' = TupE [in_z; in_stack'] $> in_tup in
  let lhs' = CaseE (in_mixop, in_tup') $> lhs in
  animate_rule_red envr ((rule_id, binds @ binds', lhs', out_stack', prems') $> r)

(* $step_ctxt: config -> config *)
let transform_step_ctxt_clause id envr (c: clause) : func_clause =
  let DefD (binds, [{it = ExpA lhs; _}], rhs, prems) = c.it in
  let CaseE (out_mixop, out_tup) = rhs.it in
  let CaseE (in_mixop, in_tup) = lhs.it in
  let TupE [in_z; in_stack] = in_tup.it in
  let TupE [out_z; out_stack] = out_tup.it in
  let binds', in_stack', out_stack', prems' = transform_step_vals envr in_stack out_stack prems in
  let in_tup' = TupE [in_z; in_stack'] $> in_tup in
  let lhs' = CaseE (in_mixop, in_tup') $> lhs in
  let out_tup' = TupE [out_z; out_stack'] $> out_tup in
  let rhs' = CaseE (out_mixop, out_tup') $> rhs in
  animate_clause id envr (DefD (binds @ binds', [expA lhs'], rhs', prems) $> c)


let animate_rule envr at rel_id rule_name (r: rule_clause) : func_clause =
  let (rule_id, _, _, _, _) = r.it in
  if is_unanimatable "rule_lhs" rule_id.it rel_id then
    animate_rule_red_no_arg envr r
  else if is_step_rule rel_id then
    transform_step_rule envr r
  else if is_step_pure_rule rel_id then
    transform_step_pure_rule envr r
  else if is_step_read_rule rel_id then
    transform_step_read_rule envr r
  else
    animate_rule_red envr r

let animate_rules envr at rel_id rule_name rs = List.map (animate_rule envr at rel_id rule_name) rs



let animate_rule_def envr (rdef: rule_def) : func_def =
  let (rule_name, rel_id, t1, t2, rules) = rdef.it in
  let params = [ExpP ("_" $ t1.at, t1) $ t1.at] in
  if List.mem rel_id.it Common.step_relids then
    ((rel_id.it ^ "/" ^ rule_name) $> rel_id, params, t2,
     animate_rules envr rdef.at rel_id.it rule_name rules, None) $ rdef.at
  else
    (rel_id, params, t2,
     animate_rules envr rdef.at rel_id.it rule_name rules, None) $ rdef.at


let animate_func_def' envr (id, ps, typ, clauses, opartial) =
  match id.it with
  | "step_ctxt" -> (id, ps, typ, List.map (transform_step_ctxt_clause id envr) clauses, opartial)
  | _           -> (id, ps, typ, List.map (animate_clause             id envr) clauses, opartial)
let animate_func_def envr (hdef: func_def) : func_def = animate_func_def' envr hdef.it $ hdef.at


let rec animate_def envr (d: dl_def): dl_def = match d with
| TypeDef tdef -> TypeDef tdef
| RuleDef rdef -> FuncDef (animate_rule_def envr rdef)
| FuncDef fdef -> FuncDef (animate_func_def envr fdef)
| RecDef  defs -> RecDef (List.map (animate_def envr) defs)


(* Merge all rules that have the same rel_id.
   We've generated functions for each rule_name like:
     $Rel_id/rule_name1(params) : t
     $Rel_id/rule_name2(params) : t
   We also want to create an umbralla function definition that tries all
   different rules, like:
     $Rel_id(params) : t
     $Rel_id(vs) = $Rel_id/rule_name1(vs)
     $Rel_id(vs) = $Rel_id/rule_name2(vs)
   So that we can use the former more efficient version when we want,
   and leave the rest to the latter more pattern-match heavy one.
   This requires a special semantics in the interpreter, that
   even the patterns all overlap, if a clause fails, it still falls
   through to try later cases. It is a bit tricky to directly translate
   it into OCaml though.
*)
let rec merge_defs (defs: dl_def list) : dl_def list =
  match defs with
  | [] -> []
  | (FuncDef {it = (fid0, params, typ, _, opartial); _} as f) :: fs ->
    let rel_id = function
    | FuncDef {it = (fid, _, _, _, _); _} -> Some (String.split_on_char '/' fid.it |> List.hd)
    | _ -> None
    in
    let rel_id0 = String.split_on_char '/' fid0.it |> List.hd in
    let fs_same, fs_diff =
      List.partition (fun f -> rel_id f = Some rel_id0) fs in
    let fs =
      if List.mem rel_id0 Common.step_relids then
        let mk_clause = function
        | FuncDef {it = (fid, ps, t, _, _); at; _} ->
          let args, binds = List.map (fun p -> (match p.it with
            | ExpP (v, t') ->
              let v' = if v.it = "_" then fresh_id (Some "a") v.at else v in
              ExpA (VarE v' $$ v.at % t') $ p.at, ExpB (v', t') $ p.at
            | TypP s -> TypA (VarT (s, []) $ s.at) $ p.at, TypB s $ p.at
            | DefP (f, ps', t') -> DefA f $ p.at, DefB (f, ps', t') $ p.at
            | GramP (v, t') -> todo "merge_def: GramP"
            )
          ) ps |> Lib.List.unzip in
          let e = CallE (fid, args) $$ at % t in
          DefD (binds, args, e, []) $ at in
        let clauses = f :: fs_same |> List.map mk_clause in
        let at = (f :: fs_same) |> List.map (fun (FuncDef fdef) -> fdef) |> List.map at |> over_region in
        let f' = FuncDef ((rel_id0 $> fid0, params, typ, clauses, opartial) $ at) in
        f :: fs_same @ [f']
      else
        let func_clauses (FuncDef {it = (_, _, _, cls, _); _}) = cls in
        let clauses = f :: fs_same |> List.concat_map func_clauses in
        let at = (f :: fs_same) |> List.map (fun (FuncDef fdef) -> fdef) |> List.map at |> over_region in
        let f' = FuncDef ((fid0, params, typ, clauses, opartial) $ at) in
        [f']
    in
    fs @ merge_defs fs_diff
  | ((RecDef defs') as f) :: fs ->
    RecDef (merge_defs defs') :: merge_defs fs
  | f :: fs -> f :: merge_defs fs

(* Entry function *)
let animate (dl, il) =
  let envr = ref (Il.Env.env_of_script il) in
  let dl' = dl |> List.map (animate_def envr)
               |> merge_defs
  in
  (* Il2dl.list_all_dl_defs dl'; *)
  (!envr, dl')