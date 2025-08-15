open Util
open Error
open Lib.Fun
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
        "op"
      ]

let error at msg = Error.error at "IL animation" msg
let error_np msg = error no_region msg

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

module type S = sig
  type t
  val init : unit -> t
end

module State (S : S) : Lib.MonadState with type s = S.t = struct
  type s = S.t
  type 'a m = State of (s -> ('a * s))
  let state f = State f
  let run_state (State m) s = m s
  let get () = state (fun s -> (s, s))
  let put s = state (fun _ -> ((), s))
  let return a = state (fun s -> (a, s))
  let ( >>= ) ma f = state (fun s -> let (a, s') = run_state ma s in
                                     run_state (f a) s')
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let mapM f = Fun.flip (List.fold_right (fun a m -> let* x = f a in
                                                     let* xs = m in
                                                     return (x::xs)))
                        (return [])
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs
  let update f = let* s = get () in put (f s)
  let update_get_old f = let* s = get () in put (f s) >> return s
  let update_get_new f = let* s = get () in let s' = f s in put s' >> return s'
end

module type E = sig
  type t
  val string_of_error : t -> string
end

module type ExceptT = functor (E : E) (M : Lib.Monad) -> sig
  (* Just repeat the MonadTrans signature, because it's a functor and it cannot
     be easily included. *)
  include Lib.Monad
  val lift : 'a M.m -> 'a m

  (* Extra interfaces *)
  val run_exceptT : 'a m -> (('a, E.t) result) M.m
  val exceptT :  (('a, E.t) result) M.m -> 'a m
  val throw : E.t -> 'a m
end

module ExceptT : ExceptT = functor (E : E) (M : Lib.Monad) -> struct
  open Result
  type 'a m = ExceptT of (('a, E.t) result) M.m
  let run_exceptT (ExceptT m) = m
  let exceptT m = ExceptT m
  let return x = ExceptT (Ok x |> M.return)
  let ( >>= ) ma f = ExceptT (
    let open M in
    run_exceptT ma >>= function
    | Error e -> return (Error e)
    | Ok    a -> run_exceptT (f a))
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let mapM f = Fun.flip (List.fold_right (fun a m -> let* x = f a in
                                                     let* xs = m in
                                                     return (x::xs)))
                        (return [])
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs
  let lift m = ExceptT (let open M in let* x = m in return (Ok x))
  let throw e = ExceptT (M.return (Error e))
end

module AnimError : E with type t = string = struct
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
  let push_prems : prem -> t -> t = fun p t ->
    let ps = get_prems t in
    let ps' = p::ps in
    put_prems ps' t
  let pop_prems : t -> (prem * t) = fun t ->
    let ps = get_prems t in
    match ps with
    | [] -> error_np "no premise to pop from the stack."
    | p::ps' -> let t' = put_prems ps' t in (p, t')
  let peek_prems : t -> prem = fun t ->
    let ps = get_prems t in
    match ps with
    | [] -> error_np "no premise to peek from the stack."
    | p::_ -> p
  let enqueue_prems : prem -> t -> t = fun p t ->
    let ps = get_prems t in
    put_prems (ps @ [p]) t

  let get_prems' : t -> prem list = fun t -> t.prems'
  let put_prems' : prem list -> t -> t = fun ps t -> { t with prems' = ps }
  let push_prems' : prem -> t -> t = fun p t ->
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

module AnimateS = State(AnimState)
module AnimateE = ExceptT(AnimError)(AnimateS)

module E = AnimateE
module S = AnimateS



(* Helpers *)

let is_varE : exp -> bool = fun e ->
  match e.it with
  | VarE _ -> true
  | _      -> false

let mk_natT at = NumT `NatT $ at

let mk_natE at (n: int) = NumE (`Nat (Z.of_int n)) $$ at % (mk_natT at)

(* ASSUMES: [e] has numtype [t1]. *)
let cvt e t1 t2 at = if t1 = t2 then e else CvtE (e, t1, t2) $$ at % (NumT t2 $ at)

(* When e1 and e2 are both `NatT, we want to construct e1 - e2, with both of them
   converted to `IntT, and then convert the result back to `NatT.
*)
let cvt_sub at e1 e2 =
  let e1' = cvt e1 `NatT `IntT e1.at in
  let e2' = cvt e2 `NatT `IntT e2.at in
  let e = BinE (`SubOp, `IntT, e1', e2') $$ at % (NumT `IntT $ at) in
  cvt e `IntT `NatT at


let is_unary_tupT : typ -> bool = fun t ->
  match t.it with
  | TupT [_] -> true
  | _        -> false

let is_unary_variantT : deftyp -> bool = fun deft ->
  match deft.it with
  | VariantT [_] -> true
  | _            -> false

let iter_elt_typ env t : typ =
  match (reduce_typ env t).it with
  | IterT (t', (List | List1 | ListN _)) -> t'
  | _ -> error t.at ("Input type is not an iterated type: " ^ string_of_typ t)

let as_iter_typ iter env t : typ =
  match (reduce_typ env t).it with
  | IterT (t1, iter') when Il.Eq.eq_iter iter iter' -> t1
  | _ -> error t.at ("Input type is not an iterated " ^ string_of_iter iter ^ " type: " ^ string_of_typ t)

let as_variant_typ env t : typcase list =
  match (reduce_typdef env t).it with
  | VariantT tcs -> tcs
  | _ -> error t.at ("Input type is not a variant type: " ^ string_of_typ t)

let as_tup_typ env t : (exp * typ) list =
  match (reduce_typ env t).it with
  | TupT ets -> ets
  | _ -> error t.at ("Input type is not a tuple type: " ^ string_of_typ t)



(* FIXME(zilinc): I don't think it handles dependent types correctly. The binds
   should be telescopic.
*)
let binds_of_env env : bind list =
  let varbinds = Map.to_list env.vars in
  List.map (fun (v, t) -> ExpB (v $ no_region, t) $ no_region) varbinds

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
  | ErrorCycle ls -> error no_region ("Cyclic dependency in binders: " ^ string_of_id id)



let new_bind_exp' envr oname exp ot =
  let v = fresh_id oname exp.at in
  let t = match ot with Some t' -> t' | None -> exp.note in
  envr := bind_var !envr v t;
  let ve = VarE v $$ v.at % t in
  let prem_eq = IfPr (CmpE (`EqOp, `BoolT, exp, ve) $$ exp.at % (BoolT $ exp.at)) $ exp.at in
  (envr, v, ve, prem_eq)
let rec new_bind_exp envr oname exp ot : (Il.Env.t ref * id * exp * prem, id) result =
  let ( let* ) = Result.bind in
  match exp.it with
  | VarE v -> Error v
  | SubE (exp', t1, t2) ->
    assert (Option.is_none ot);
    let* (envr, v, ve, prem_eq) = new_bind_exp envr oname exp' None in
    let ve' = SubE (ve, t1, t2) $> exp in
    Ok (envr, v, ve', prem_eq)
  | SupE (exp', t1, t2) ->
    assert (Option.is_none ot);
    let* (envr, v, ve, prem_eq) = new_bind_exp envr oname exp' None in
    let ve' = SupE (ve, t1, t2) $> exp in
    Ok (envr, v, ve', prem_eq)
  | CvtE (exp', t1, t2) ->
    assert (Option.is_none ot);
    let* (envr, v, ve, prem_eq) = new_bind_exp envr oname exp' None in
    let ve' = CvtE (ve, t1, t2) $> exp in
    Ok (envr, v, ve', prem_eq)
  | _ -> Ok (new_bind_exp' envr oname exp ot)


let get () = S.get () |> E.lift
let put s  = S.put s  |> E.lift
let update f = S.update f |> E.lift

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
  let* () = update f_begin in
  let* a = ma in
  let* () = update f_end in
  E.return a

let string_of_state (s: AnimState.t) =
  "prems   : length: " ^ string_of_int (List.length s.prems) ^ "\n" ^
  "prems'  : length: " ^ string_of_int (List.length s.prems') ^ "\n" ^
  "knowns  : " ^ string_of_varset s.knowns ^ "\n" ^
  "progress: " ^ string_of_bool s.progress ^ "\n" ^
  "inverse : " ^ string_of_bool s.inverse

let throw_log e = let () = info "log" no_region e in E.throw e

(* A whitelist of rules/defs that cannot be easily animated.
   The map is "reason" ↦ [("rel_id", "rule_name")]
*)
let cannot_animate : (string * string) list Map.t =
  Map.of_list
    [ ("rule_lhs",
      [
        ("Step_pure", "br-label-zero");
        ("Step_pure", "br-label-succ");
        ("Step_pure", "br-handler");

        ("Step_read", "return_call_ref-label");
        ("Step_read", "return_call_ref-handler");
        ("Step_read", "return_call_ref-frame-null");
        ("Step_read", "return_call_ref-frame-addr");

        ("Step_pure", "return-frame");
        ("Step_pure", "return-label");
        ("Step_pure", "return-handler");

        ("Step_read", "throw_ref-instrs");
      ])
    ]

let is_unanimatable reason rule_name rel_id : bool =
  match Map.find_opt reason cannot_animate with
  | None -> false
  | Some ls -> List.exists (fun l -> l = (rel_id, rule_name)) ls


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
  | true , false -> E.return (cvt e2 t t' e2.at, cvt e1 t t' e1.at)
  | false, true  -> E.return (cvt e1 t t' e1.at, cvt e2 t t' e1.at)
  | false, false -> E.throw (string_of_error at
                               ("Can't animate binary expression where both operands contain unknowns:\n" ^
                                "  ▹ op = " ^ string_of_binop (op :> binop) ^ "\n" ^
                                "  ▹ e1 = " ^ string_of_exp e1 ^ " (unknowns: " ^ string_of_varset unknowns_e1 ^ ")\n" ^
                                "  ▹ e2 = " ^ string_of_exp e2 ^ " (unknowns: " ^ string_of_varset unknowns_e2 ^ ")"))
  in
  let rhs'' = BinE (op', (t' :> optyp), cvt rhs t t' rhs.at, rhs') $$ rhs.at % lhs'.note in
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
(* We don't allow inverting rules, so the LHS (i.e. all args expect the last one)
   of a rule must be known.
*)
let rec animate_rule_prem envr at id mixop exp : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let (rhs, fncall) = match id.it, exp.it with
  | _, TupE [lhs; rhs] when List.mem id.it ["Step"; "Step_read"; "Step_pure"] ->
    let fncall = CallE (id, [ExpA lhs $ lhs.at]) $$ at % rhs.note in
    (rhs, fncall)
  | "Expand", TupE [lhs; rhs] ->
    let fid = "expanddt" $ id.at in
    let fncall = CallE (fid, [ExpA lhs $ lhs.at]) $$ at % rhs.note in
    (rhs, fncall)
  | "Eval_expr", TupE [lhs; rhs] ->
    let fncall = CallE (id, [ExpA lhs $ lhs.at]) $$ at % rhs.note in
    (rhs, fncall)
  (* Other rules, mostly from validation *)
  | _, TupE es when List.length es >= 2 ->
    let lhss, rhs = Lib.List.split_last es in
    let expA (e: exp) = ExpA e $ e.at in
    let fncall = CallE (id, List.map expA lhss) $$ at % rhs.note in
    (rhs, fncall)
  | _ -> error at ("Unknown rule form: " ^ id.it ^ "(" ^ string_of_region id.at ^")")
  in
  (* Let RHS = $call(LHS) *)
  let unknowns_rhs    = Set.diff (free_exp false rhs   ).varid knowns in
  let unknowns_fncall = Set.diff (free_exp false fncall).varid knowns in
  if not (Set.is_empty unknowns_rhs) && Set.is_empty unknowns_fncall then
    (* When satisfying the precondition of `animate_exp_eq`. *)
    animate_exp_eq envr at rhs fncall
  else if Set.is_empty unknowns_rhs && Set.is_empty unknowns_fncall then
    (* The rule is fully known, then check. *)
    animate_if_prem envr at (CmpE (`EqOp, `BoolT, rhs, fncall) $$ at % (BoolT $ at))
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
  let* s = get () in
  let knowns = get_knowns s in
  match lhs.it with
  (* Base case: single variable assignment. *)
  | VarE v ->
    let* () = update (add_knowns (Set.singleton v.it)) in
    E.return [ LetPr (lhs, rhs, [v.it]) $ at ]
  (* function call; invert it. *)
  | CallE (fid, args) when can_invert s ->
    let varid = fun s -> s.varid in
    let fv_args = List.map (free_arg false) args |> List.map varid in
    let unknowns = List.map (fun fv_arg -> Set.diff fv_arg knowns) fv_args in
    let oinv_fid = find_func_hint !envr fid.it "inverse" in
    let* inv_fid = match oinv_fid with
    | None -> E.throw (string_of_error at ("No inverse function declared for `" ^ fid.it ^ "`, so can't invert it."))
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
    | ListN(len, Some i) ->
      let fv_len = (free_exp false len).varid in
      let unknowns_len = Set.diff fv_len knowns in
      if Set.is_empty unknowns_len then
        (* Base case for iterators *)
        let t = reduce_typ !envr lhs'.note in
        let rhs' = IdxE (rhs, VarE i $$ i.at % (mk_natT i.at)) $$ rhs.at % lhs'.note in
        let prem_body = IfPr (CmpE (`EqOp, `BoolT, lhs', rhs') $$ at % (BoolT $ at)) $ at in
        bracket (add_knowns (Set.singleton i.it))
                (remove_knowns (Set.singleton i.it))
                (animate_prem envr (IterPr ([prem_body], iterexp) $ at))
      else
        (* Inductive case where [len] is unknown. *)
        let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
        let* prem_len = animate_exp_eq envr len.at len len_rhs in
        (* By now [len] should be known. *)
        let* prems' = animate_exp_eq envr at lhs rhs in
        E.return (prem_len @ prems')
    | Opt ->
      let rhs' = TheE rhs $$ rhs.at % (as_iter_typ Opt !envr rhs.note) in
      let prem_body = IfPr (CmpE (`EqOp, `BoolT, lhs', rhs') $$ at % (BoolT $ at)) $ at in
      animate_prem envr (IterPr ([prem_body], iterexp) $ at)
    (* Inductive cases *)
    | ListN(len, None) ->
      let i = fresh_id (Some "i") at in
      let i_star = Frontend.Dim.annot_varid i [iter] in
      let t_star = IterT (mk_natT i_star.at, List) $ i_star.at in
      let i_star_e = VarE i_star $$ i_star.at % t_star in
      envr := bind_var !envr i_star t_star;
      let xes' = (i, i_star_e) :: xes in
      animate_exp_eq envr at (IterE (lhs', (ListN(len, Some i), xes')) $> lhs) rhs
    | List | List1 ->
      let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
      let len_v = fresh_id (Some "len") len_rhs.at in
      envr := bind_var !envr len_v (mk_natT len_rhs.at);
      let len = VarE len_v $$ len_rhs.at % len_rhs.note in
      let* prems_len_v = animate_exp_eq envr len.at len len_rhs in
      let oprem_len = match iter with
      | List  -> None
      | List1 -> Some (IfPr (CmpE (`GeOp, `NatT, len, mk_natE len.at 1) $$ len.at % (BoolT $ len.at)) $ at)
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
    let rhs' = SupE (rhs, t2, t1) $$ rhs.at % t1 in
    animate_exp_eq envr at exp rhs'
  | SupE (exp, t1, t2) ->
    let rhs' = SubE (rhs, t2, t1) $$ rhs.at % t1 in
    animate_exp_eq envr at exp rhs'
  | OptE None -> assert false  (* Because lhs must contain unknowns *)
  | OptE (Some exp) ->
    begin match new_bind_exp envr None exp None with
    | Ok (envr, v, ve, prem_v) ->
      let prem_opt = LetPr (OptE (Some ve) $$ lhs.at % rhs.note, rhs, [v.it]) $ at in
      let* () = update (add_knowns (Set.singleton v.it)) in
      let* prems' = animate_prem envr prem_v in
      E.return (prem_opt :: prems')
    | Error v ->
      let* () = update (add_knowns (Set.singleton v.it)) in
      E.return [LetPr (lhs, rhs, [v.it]) $ at]
    end
  | ListE [] ->
    assert false  (* Because lhs must contain unknowns. *)
  | ListE exps ->
    let* (envr, ve, prems_rhs) = begin match new_bind_exp envr None rhs None with
    | Ok (envr, v, ve, prem_v) ->
      let* prems_v' = animate_prem envr prem_v in
      E.return (envr, ve, prems_v')
    | Error v -> E.return (envr, rhs, [])
    end in
    (* We need a length check to serve as the irrefutable list pattern. *)
    let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
    let len_lhs = mk_natE lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`EqOp, `BoolT, len_lhs, len_rhs) $$ at % (BoolT $ at)) $ at in
    let prems = List.mapi (fun i exp ->
          let ie = mk_natE exp.at i in
          IfPr (CmpE (`EqOp, `BoolT, exp, IdxE (ve, ie) $$ ve.at % exp.note)
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
    E.return (prems_rhs @ [prem_len] @ prems')
  | CaseE (mixop, lhs') ->
    begin match as_variant_typ !envr rhs.note with
    | [] -> assert false
    | [(mixop', (_, t, _), _)] when Il.Eq.eq_mixop mixop mixop' ->
      animate_exp_eq envr at lhs' (UncaseE (rhs, mixop) $$ rhs.at % lhs'.note)
    | tcases ->
      begin match lhs'.it with
      (*
      | TupE es ->
        let (_, (bs, t', _), _) = List.find (fun (mixop', _, _) -> Il.Eq.eq_mixop mixop mixop') tcases in
        let ets = as_tup_typ !envr t' in
        let* (envr, vs, ves, prem_vs) = E.foldlM (fun acc (e, (_, t)) ->
          let (envr, vs, ves, prem_vs) = acc in
          let (envr, v, ve, prem_v) = new_bind_exp envr None e (Some t) in
          let* () = update (add_knowns (Set.singleton v.it)) in
          E.return (envr, vs@[v.it], ves@[ve], prem_vs@[prem_v])
        ) (envr, [], [], []) (List.combine es ets) in
        let prem_case = LetPr (CaseE (mixop, TupE ves $$ lhs'.at % lhs'.note) $$ lhs.at % rhs.note, rhs, vs) $ at in
        let envr = env_of_binds bs envr in
        let* prems' = E.mapM (animate_prem envr) prem_vs in
        E.return (prem_case :: List.concat prems')
      *)
      | _ ->
        (* Use tcases to work out the type of ve, because it retains the dependent tuple type. *)
        let (_, (bs, t', _), _) = List.find (fun (mixop', _, _) -> Il.Eq.eq_mixop mixop mixop') tcases in
        begin match new_bind_exp envr None lhs' (Some t') with
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
      end
    end
  | TupE es ->
    (* Bind to a new variable, so that [rhs] doesn't need to be re-evaluated
       again and again in the following projections.
    *)
    let* (envr, ve, prems_rhs) = begin match new_bind_exp envr None rhs None with
    | Ok (envr, v, ve, prem_v) ->
      let* prems_v = animate_exp_eq envr at ve rhs in
      E.return (envr, ve, prems_v)
    | Error v ->
      E.return (envr, rhs, [])
    end in
    let prems = Fun.flip List.mapi es (fun i e ->
      let bool_t = BoolT $ e.at in
      let proj_rhs = ProjE (ve, i) $$ ve.at % e.note in
      IfPr (CmpE (`EqOp, `BoolT, e, proj_rhs) $$ e.at % bool_t) $ at)
    in
    (* We start an inner loop to animate the components of TupE. This is needed
       if we have premises like `(... x ..., x) = (e1, e2)`, where the first
       component cannot be animated when `x` is unknown. By solving the second
       first, we turn the first into a check.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems; knowns = get_knowns s' } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prems_rhs @ prems')
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
    let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
    let len_lhs1 = mk_natE lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`GeOp, `NatT, len_lhs1, len_rhs) $$ len_rhs.at % (BoolT $ len_rhs.at)) $ len_rhs.at in
    let prems1 = List.mapi (fun i exp ->
      let idx = NumE (`Nat (Z.of_int i)) $$ exp.at % (mk_natT exp.at) in
      let rhs' = IdxE (rhs, idx) $$ exp.at % exp.note in
      IfPr (CmpE (`EqOp, `BoolT, exp, rhs') $$ exp.at % (BoolT $ exp.at)) $ at
    ) exps in
    let start2 = NumE (`Nat (Z.of_int (List.length exps))) $$ exp1.at % (mk_natT exp1.at) in
    let len2 = cvt_sub exp2.at len_rhs start2 in
    let rhs2' = SliceE (rhs, start2, len2) $$ rhs.at % rhs.note in
    let prem2 = IfPr (CmpE (`EqOp, `BoolT, exp2, rhs2') $$ exp2.at % (BoolT $ exp2.at)) $ at in
    (* Start an inner loop, in case of any dependencies between the list elements.
       E.g. -- if [v, v] v'* = rhs
       The first [v] is a binding, and the second becomes a check.
    *)
    let s_new = { (init ()) with prems = prems1 @ [prem2]; knowns = get_knowns s } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prem_len :: prems')
  (* exp1 ++ [e1; e2; ...; en] *)
  | CatE (exp1, ({ it = ListE exps; _ } as exp2)) ->
    let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
    let len_lhs2 = mk_natE lhs.at (List.length exps) in
    let prem_len = IfPr (CmpE (`GeOp, `NatT, len_lhs2, len_rhs) $$ len_rhs.at % (BoolT $ len_rhs.at)) $ len_rhs.at in
    let prems2 = List.mapi (fun i exp ->
      let idx = NumE (`Nat (Z.of_int i)) $$ exp.at % (mk_natT exp.at) in
      (* idx' = len - (len2 - idx) *)
      let idx' = cvt_sub len_lhs2.at len_rhs (cvt_sub len_lhs2.at len_lhs2 idx) in
      let rhs' = IdxE (rhs, idx') $$ exp.at % exp.note in
      IfPr (CmpE (`EqOp, `BoolT, exp, rhs') $$ exp.at % (BoolT $ exp.at)) $ at
    ) exps in
    let start1 = NumE (`Nat (Z.of_int 0)) $$ no_region % (mk_natT no_region) in
    let len1 = cvt_sub exp1.at len_rhs len_lhs2 in
    let rhs1' = SliceE (rhs, start1, len1) $$ rhs.at % rhs.note in
    let prem1 = IfPr (CmpE (`EqOp, `BoolT, exp1, rhs1') $$ exp1.at % (BoolT $ exp1.at)) $ at in
    (* Start an inner loop, in case of any dependencies between the list elements.
    *)
    let s_new = { (init ()) with prems = prems2 @ [prem1]; knowns = get_knowns s } in
    let* (prems', s_new') = run_inner s_new (animate_prems' envr at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return (prem_len :: prems')
  | _ -> E.throw (string_of_error at ("Can't pattern match or compute LHS: " ^ string_of_exp lhs))

(** ASSUMES: [e] contains unknown vars, whereas [es] is fully known.
    ENSURES: When it returns Error, it means that the original premise should be
    used as the animated premise.
 *)
and animate_exp_mem at e es : prem list E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  match e.it with
  (* Base case: choose the first alternative. *)
  | VarE v ->
    let zero = NumE (`Nat Z.zero) $$ e.at % (mk_natT e.at) in
    let es_0 = IdxE (es, zero) $$ es.at % e.note in
    let fv_e = (free_exp false e).varid in
    let* () = update (add_knowns (Set.singleton v.it)) in
    E.return [ LetPr (e, es_0, [v.it]) $ at ]
  | _ ->
    (* TODO(zilinc): E.g. (x, a) ∈ e, where a is known and x is unknown, e is fully known.
       It will become Let (x, a) = y ; Let y ∈ e. It is obviously not animated.
    *)
    E.throw (string_of_error at "Can't handle `<-` operator when the LHS has knowns and unknowns.")

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
  (* Break up conjunctions. We have to push the two conjuncts on the stack
     and hand over the control to the outer loops, because these two conjuncts
     may need to be animated in different iterations.
   *)
  | BinE (`AndOp, _, e1, e2) ->
    (* This should be the only place that we manipulate the stack, because the conjuncts
       are totally independent of each other and can be flattened into the main loop.
     *)
    let* () = update (push_prems (IfPr e2 $ e2.at) >>>
                      push_prems (IfPr e1 $ e1.at)) in
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
    | false, true  -> animate_exp_mem exp.at e1 e2
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
  | IterPr ([prem'], ((iter, xes) as iterexp)) ->
    let iter' = match iter with Opt -> Opt | _ -> List in
    let lenvr = ref !envr in
    (* Propagating knowns into the iteration. *)
    let oindex = match iter with
    | ListN(len, Some i) ->
      lenvr := bind_var !lenvr i (mk_natT len.at);
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
    let s_body = { (init ()) with prems = [prem']; knowns = knowns_inner_idx } in
    let* (prems_body', s_body') = run_inner s_body (animate_prems' lenvr prem'.at) in
    let new_binds = Il.Env.diff !lenvr.vars !envr.vars in
    (* NOTE the side effect of updating [envr]. *)
    let xes' = List.concat_map (fun (x, t) ->
      let x_star = Frontend.Dim.annot_varid (x $ no_region) [iter] in
      let t_star = IterT (t, iter') $ x_star.at in
      envr := bind_var !envr x_star t_star;
      if List.exists (fun (x', _) -> x'.it = x) xes then [] else
        [(x $ x_star.at, VarE x_star $$ x_star.at % t_star)]
    ) (Map.to_list new_binds) in
    (* Propagate knowns to the outside of the iterator. We need to traverse [new_knowns]
       instead of [xes], because there may be variables that need to flow
       out but do not ∈ xes.
    *)
    let knowns_inner' = get_knowns s_body' in
    (* The extra variables that've been newly worked out inside the interation.
       CAUTION: If the index [i] exists, then this [i] shouldn't be propagated out.
       That's why we need to subtract the [knowns_inner_idx] set which includes
       the index, if there is one.
    *)
    let new_knowns = Set.diff knowns_inner' knowns_inner in
    let blob = List.map (fun x ->
      match List.find_opt (fun (y, e) -> y.it = x) xes with
      (* If x <- e exists, then x propagates to e. *)
      | Some (y, e) ->
        let fv_e = (free_exp false e).varid in
        let unknowns_e = Set.diff fv_e knowns_inner' in
        if Set.is_empty unknowns_e then
          (* [e] already known; nothing to flow out. *)
          ([], [])
        else
          begin match e.it with
          | VarE ve -> ([ve.it], [])
          | _ ->
            (* If [e] is not a single variable and it's out-flowing in {x <- e},
               then we create a fresh [v], such that {x <- v}, and -- if v = e
               after we finish the interation.
            *)
            let y' = Frontend.Dim.annot_varid y [iter] in
            let v = fresh_id (Some y'.it) e.at in
            envr := bind_var !envr y' e.note;
            let ve = VarE v $$ e.at % e.note in
            let prem_e = IfPr (CmpE (`EqOp, `BoolT, e, ve) $$ e.at % (BoolT $ e.at)) $ e.at in
            ([y'.it], [prem_e])
          end
      (* If there's no x <- e, then propagate x out. But I don't think this will ever
         happen, as in this case, the [x] can't be a newly-learned variable, but must
         have been known before we entered the iteration body.
      *)
      | None -> ([x], [])
    ) (Set.elements new_knowns) in
    let knowns_outer, e_prems = Lib.List.unzip blob |> Lib.Fun.(<***>) List.concat List.concat in
    let* () = update (add_knowns (Set.of_list knowns_outer)) in
    let* s_outer = get () in
    let s_end = { (init ()) with prems = e_prems; knowns = get_knowns s_outer} in
    let* (e_prems', s_end') = run_inner s_end (animate_prems' envr prem.at) in
    let* () = update (put_knowns (get_knowns s_end')) in
    E.return ((IterPr (prems_body', (iter, xes @ xes')) $ prem.at) :: e_prems')
  | IterPr (prems, iterexp) -> assert false


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
           let (prem, s') = pop_prems s in
           let* () = S.put s' in
           let* r = animate_prem envr prem |> E.run_exceptT in
           match r with
           | Error e ->
             (* Recover from failure. *)
             let* () = S.update (push_prems' prem >>> set_failure e) in
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
                      "  ▹ result: " ^ (String.concat "\n      " (List.map string_of_prem ps)) ^ "\n" ^
                      "  ▹ ins: " ^ string_of_varset ins ^ "\n" ^
                      "  ▹ knowns: " ^ string_of_varset s.knowns ^ "\n" ^
                      "  ▹ outs: " ^ string_of_varset ous)

let lift_otherwise_prem prems =
  let is_otherwise = function { it = ElsePr; _ } -> true | _ -> false in
  let (ow_pr, rest) = List.partition is_otherwise prems in
  ow_pr @ rest

(* The variant that doesn't try to animate the [lhs] of the rule, as we know that
   it's very difficult.
*)
let animate_rule_red_no_arg envr rule : clause' =
  let lenvr = ref !envr in
  let (id, binds, lhs, rhs, prems) = rule.it in
  let lhs_vars = (free_exp false lhs).varid in
  let rhs_vars = (free_exp false rhs).varid in
  (* Input and output variables in the conclusion *)
  let in_vars  = lhs_vars in
  let out_vars = rhs_vars in
  let prems' = animate_prems lenvr rule.at in_vars out_vars prems in
  let binds' = binds_of_env !lenvr in
  let binds'' = sort_binds id (binds @ binds') in
  DefD (binds'', [ExpA lhs $ lhs.at], rhs, prems')

let animate_rule_red envr rule : clause' =
  let lenvr = ref !envr in
  let (id, binds, lhs, rhs, prems) = rule.it in
  let (lenvr, v, ve, prems_lhs) = begin match new_bind_exp lenvr (Some "lhs") lhs None with
  | Ok (lenvr, v, ve, prem_v) -> (lenvr, v, ve, [prem_v])
  | Error v -> (lenvr, v, lhs, [])
  end in
  let rhs_vars = (free_exp false rhs).varid in
  (* Input and output variables in the conclusion *)
  let in_vars = (free_varid v).varid in
  let out_vars = rhs_vars in
  let prems' = animate_prems lenvr rule.at in_vars out_vars (prems_lhs @ prems) in
  let binds' = binds_of_env !lenvr in
  let binds'' = sort_binds id (binds @ binds') in
  DefD (binds'', [ExpA ve $ ve.at], rhs, prems')

let animate_rule envr at rel_id (r : rule_clause) : clause =
  let (rule_id, _, _, _, _) = r.it in
  let clause' =
    if is_unanimatable "rule_lhs" rule_id.it rel_id then
      animate_rule_red_no_arg envr r
    else
      animate_rule_red envr r
  in
  clause' $ at

let animate_rules envr at rel_id rs = List.map (animate_rule envr at rel_id) rs

let animate_clause_no_arg id envr (c: clause) : func_clause =
  let lenvr = ref !envr in
  let DefD (binds, args, exp, prems) = c.it in
  let ins = (free_list (free_arg false) args).varid in
  let ous = (free_exp false exp).varid in
  let prems' = animate_prems lenvr c.at ins ous prems |> lift_otherwise_prem in
  let binds' = binds_of_env !lenvr in
  let binds'' = sort_binds id (binds @ binds') in
  (DefD (binds'', args, exp, prems')) $ c.at

let animate_clause id envr (c: clause) : func_clause =
  let lenvr = ref !envr in
  let DefD (binds, args, exp, prems) = c.it in
  let n_args = List.length args in
  let blob = List.mapi (fun i arg -> match arg.it with
    | ExpA exp' ->
      begin match new_bind_exp lenvr (Some ("a" ^ string_of_int i)) exp' None with
      | Ok (_lenvr, v, ve, prem_v) ->
        let fv_exp' = (free_exp false exp').varid in
        (ExpA ve $ v.at, Some prem_v, Some v, fv_exp')
      | Error v -> (arg, None, Some v, Set.empty)
      end
    | _ -> (arg, None, None, Set.empty)
  ) args
  in
  let (args', o_prem_args, ovs, fv_args) = Lib.List.unzip4 blob in
  let prems_args = List.filter_map Fun.id o_prem_args in
  let vs = List.filter_map Fun.id ovs in
  let ins = (free_list free_varid vs).varid in
  let ous = (free_exp false exp).varid in
  let prems' = animate_prems lenvr c.at ins ous (prems_args @ prems) |> lift_otherwise_prem in
  let binds' = binds_of_env !lenvr in
  let binds'' = sort_binds id (binds @ binds') in
  (DefD (binds'', args', exp, prems')) $ c.at

let animate_clauses id envr cs = List.map (animate_clause id envr) cs

let animate_rule_def envr (rdef: rule_def) : func_def =
  let (_, rel_id, t1, t2, rules) = rdef.it in
  let params = [ExpP ("_" $ t1.at, t1) $ t1.at] in
  (rel_id, params, t2, animate_rules envr rdef.at rel_id.it rules, None) $ rdef.at

let animate_func_def' envr (id, ps, typ, clauses, opartial) =
  (id, ps, typ, animate_clauses id envr clauses, opartial)
let animate_func_def envr (hdef: func_def) : func_def = animate_func_def' envr hdef.it $ hdef.at

let rec animate_def envr (d: dl_def): dl_def = match d with
| TypeDef tdef -> TypeDef tdef
| RuleDef rdef -> FuncDef (animate_rule_def envr rdef)
| FuncDef fdef -> FuncDef (animate_func_def envr fdef)
| RecDef  defs -> RecDef (List.map (animate_def envr) defs)


(* Merge all rules that have the same rel_id. *)
let rec merge_defs (defs: dl_def list) : dl_def list =
  match defs with
  | [] -> []
  | (FuncDef {it = (fid0, params, typ, _, opartial); _} as f) :: fs ->
    let func_id = function
    | FuncDef {it = (fid, _, _, _, _); _} -> Some fid
    | _ -> None
    in
    let func_clauses (FuncDef {it = (_, _, _, cls, _); _}) = cls in
    let fs_same, fs_diff =
      List.partition (fun f -> func_id f = Some fid0) fs in
    let clauses = f :: fs_same |> List.concat_map func_clauses in
    let at = (f :: fs_same) |> List.map (fun (FuncDef fdef) -> fdef) |> List.map at |> over_region in
    let f' = FuncDef ((fid0, params, typ, clauses, opartial) $ at) in
    f' :: merge_defs fs_diff
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
  dl'