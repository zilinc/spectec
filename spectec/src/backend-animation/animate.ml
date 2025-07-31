open Util
open Error
open Lib.Fun
open Source
open Il.Ast
open Il.Eval
open Il.Print
open Xl.Atom
open Il2al.Def
open Il2al.Free
open Backend_ast



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


(* Environment *)

(* Global r/o store for all the whole SpecTec spec. *)
let env : Il.Env.t ref = ref Il.Env.empty

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

let rec vartyp_arg v arg : typ option =
  match arg.it with
  | ExpA exp -> vartyp_exp v exp
  | TypA _ | DefA _ | GramA _ -> None

and vartyp_exp v exp : typ option =
  match exp.it with
  | VarE id when id.it = v
  -> Some exp.note
  | VarE _ | BoolE _ | NumE _ | TextE _
  -> None
  | UnE (_, _, exp)
  | ProjE (exp, _)
  | CaseE (_, exp)
  | UncaseE (exp, _)
  | TheE exp
  | DotE (exp, _)
  | LiftE exp
  | LenE exp
  -> vartyp_exp v exp
  | BinE (_, _, exp1, exp2)
  | CmpE (_, _, exp1, exp2)
  | CompE (exp1, exp2)
  | MemE (exp1, exp2)
  | UpdE (exp1, _, exp2)
  | CatE (exp1, exp2)
  | ExtE (exp1, _, exp2)
  | IdxE (exp1, exp2)
  -> Lib.Option.mplus (vartyp_exp v exp1) (vartyp_exp v exp2)
  | TupE exps | ListE exps
  -> Lib.Option.mconcat_map (vartyp_exp v) exps
  | OptE oexp -> Option.map (vartyp_exp v) oexp |> Option.join
  | StrE expfields
  -> let exps = List.map snd expfields in
     Lib.Option.mconcat_map (vartyp_exp v) exps
  | SliceE (exp1, exp2, exp3)
  -> Lib.Option.mconcat_map (vartyp_exp v) [exp1; exp2; exp3]
  | CallE (_, args)
  -> Lib.Option.mconcat_map (vartyp_arg v) args
  | IterE (exp, (iter, xes))
  -> let len = match iter with
     | List | Opt | List1 -> []
     | ListN(n, _) -> [n]
     in
     let exps = List.map snd xes in
     Lib.Option.mconcat_map (vartyp_exp v) (exp :: len @ exps)
  | CvtE (exp, _, _)
  | SubE (exp, _, _)
  -> vartyp_exp v exp

let rec vartyp_prem (v: text) prem : typ option =
  match prem.it with
  | RulePr (_, _, exp) -> vartyp_exp v exp
  | IfPr exp -> vartyp_exp v exp
  | LetPr (lhs, rhs, _) -> Lib.Option.mplus (vartyp_exp v lhs) (vartyp_exp v rhs)
  | ElsePr -> None
  | IterPr (prems, iterexp) -> Lib.Option.mconcat_map (vartyp_prem v) prems


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
  Returns the inverted lhs and rhs.
 *)
let invert_bin_exp at op e1 e2 t rhs : (exp * exp) E.m =
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let fv_e1 = (free_exp false e1).varid in
  let fv_e2 = (free_exp false e2).varid in
  let unknowns_e1 = Set.diff fv_e1 knowns in
  let unknowns_e2 = Set.diff fv_e2 knowns in
  let* lhs', rhs' = match Set.is_empty unknowns_e1, Set.is_empty unknowns_e2 with
  | true , true  -> assert false
  | true , false -> E.return (e2, e1)
  | false, true  -> E.return (e1, e2)
  | false, false -> E.throw (string_of_error at
                               ("Can't animate binary expression where both operands contain unknowns:\n" ^
                                "  ▹ op = " ^ string_of_binop op ^ "\n" ^
                                "  ▹ e1 = " ^ string_of_exp e1 ^ " (unknowns: " ^ string_of_varset unknowns_e1 ^ ")\n" ^
                                "  ▹ e2 = " ^ string_of_exp e2 ^ " (unknowns: " ^ string_of_varset unknowns_e2 ^ ")"))
  in
  let* op' = match op with
  | `AddOp -> E.return `SubOp
  | `SubOp -> E.return `AddOp
  | `MulOp -> E.return `DivOp
  | `DivOp -> E.return `MulOp
  | `ModOp | `PowOp ->
    E.throw (string_of_error at ("Binary operator " ^ string_of_binop op ^ " is not invertible."))
  | `AndOp | `OrOp | `ImplOp | `EquivOp ->
    (* We can do some, if we really need to. *)
    E.throw (string_of_error at ("Binary Boolean operator " ^ string_of_binop op ^ " is not invertible in general."))
  in
  let rhs'' = BinE (op', t, rhs, rhs') $$ rhs.at % lhs'.note in
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
let rec animate_rule_prem at id mixop exp : prem list E.m =
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
    animate_exp_eq at rhs fncall
  else if Set.is_empty unknowns_rhs && Set.is_empty unknowns_fncall then
    (* The rule is fully known, then check. *)
    animate_if_prem at (CmpE (`EqOp, `BoolT, rhs, fncall) $$ at % (BoolT $ at))
  else
    E.throw (string_of_error at ("LHS of rule " ^ id.it ^ " has unknowns: " ^
                                 string_of_varset unknowns_fncall))

(** ASSUMES: [lhs] contains unknown vars, whereas [rhs] is fully known. *)
and animate_exp_eq at lhs rhs : prem list E.m =
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
    let oinv_fid = Il.Env.find_func_hint !env fid.it "inverse" in
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
        animate_exp_eq at lhs' fncall
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
        let t = reduce_typ !env lhs'.note in
        let rhs' = IdxE (rhs, VarE i $$ i.at % (mk_natT i.at)) $$ rhs.at % lhs'.note in
        let prem_body = IfPr (CmpE (`EqOp, `BoolT, lhs', rhs') $$ at % (BoolT $ at)) $ at in
        bracket (add_knowns (Set.singleton i.it))
                (remove_knowns (Set.singleton i.it))
                (animate_prem (IterPr ([prem_body], iterexp) $ at))
      else
        (* Inductive case where [len] is unknown. *)
        let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in 
        let* prem_len = animate_exp_eq len.at len len_rhs in
        (* By now [len] should be known. *)
        let* prems' = animate_exp_eq at lhs rhs in
        E.return (prem_len @ prems')
    (* Inductive cases *)
    | ListN(len, None) ->
      let i = fresh_id (Some "i") at in
      animate_exp_eq at (IterE (lhs', (ListN(len, Some i), xes)) $> lhs) rhs
    | Opt | List | List1 ->
      let len_rhs = LenE rhs $$ rhs.at % (mk_natT rhs.at) in
      let len_v = fresh_id (Some "len") len_rhs.at in
      let len = VarE len_v $$ len_rhs.at % len_rhs.note in
      let* prems_len_v = animate_exp_eq len.at len len_rhs in
      let oprem_len = match iter with
      | List  -> None
      | Opt   -> Some (IfPr (CmpE (`LeOp, `NatT, len, mk_natE len.at 1) $$ len.at % (BoolT $ len.at)) $ at)
      | List1 -> Some (IfPr (CmpE (`GeOp, `NatT, len, mk_natE len.at 1) $$ len.at % (BoolT $ len.at)) $ at)
      | _     -> assert false
      in
      let* prems_len = match oprem_len with
      | None -> E.return []
      | Some prem_len -> animate_prem prem_len
      in
      let i = fresh_id (Some "i") at in
      let* prems' = animate_exp_eq at (IterE (lhs', (ListN(len, Some i), xes)) $> lhs) rhs in
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
    let* (prems', s_new') = run_inner s_new (animate_prems' at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return prems'
  | SubE (exp, t1, t2) ->
    let rhs' = SupE (rhs, t2, t1) $$ rhs.at % t1 in
    animate_exp_eq at exp rhs'
  | SupE (exp, t1, t2) ->
    let rhs' = SubE (rhs, t2, t1) $$ rhs.at % t1 in
    animate_exp_eq at exp rhs'
  | OptE None -> assert false  (* Because lhs must contain unknowns *)
  | OptE (Some exp) ->
    let rhs' = TheE rhs $$ rhs.at % (as_iter_typ Opt !env rhs.note) in
    animate_exp_eq at exp rhs'
  | ListE [] ->
    assert false  (* Because lhs must contain unknowns. *)
  | ListE exps ->
    let len = List.length exps in
    let prems = List.mapi (fun i exp ->
          IfPr (CmpE (`EqOp, `BoolT, exp, ProjE (rhs, i) $$ rhs.at % exp.note)
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
    let s_new = { (init ()) with prems; knowns = get_knowns s } in
    let* prems', s_new' = run_inner s_new (animate_prems' at) in
    let* () = update (put_knowns (get_knowns s_new')) in
    E.return prems'
  | CaseE (mixop, lhs') ->
    animate_exp_eq at lhs' (UncaseE (rhs, mixop) $$ rhs.at % lhs'.note)
  | TupE es ->
    let v = fresh_id None at in
    (* Bind to a new variable, so that [rhs] doesn't need to be re-evaluated
       again and again in the following projections.
    *)
    let e_v = VarE v $$ v.at % rhs.note in
    let* prems_v = animate_exp_eq at e_v rhs in
    let prems = Fun.flip List.mapi es (fun i e ->
      let bool_t = BoolT $ e.at in
      let proj_rhs = ProjE (e_v, i) $$ e_v.at % e.note in
      IfPr (CmpE (`EqOp, `BoolT, e, proj_rhs) $$ e.at % bool_t) $ at)
    in
    (* We start an inner loop to animate the components of TupE. This is needed
       if we have premises like `(... x ..., x) = (e1, e2)`, where the first
       component cannot be animated when `x` is unknown. By solving the second
       first, we turn the first into a check.
    *)
    let* s' = get () in
    let s_new = { (init ()) with prems; knowns = get_knowns s' } in
    let* (prems', s_new') = run_inner s_new (animate_prems' at) in
    let knowns' = get_knowns s_new' in
    let* () = put ({ s' with knowns = knowns' }) in
    E.return (prems_v @ prems')
  | CvtE (lhs', t1, t2) ->
    (* FIXME(zilinc): Conversion is not checked. *)
    animate_exp_eq at lhs' (CvtE (rhs, t2, t1) $$ rhs.at % lhs'.note)
  (* Some operators, together with certain combinations of a known operand plus
     the known RHS, can be inverted.
  *)
  | BinE (op, t, e1, e2) ->
    let* lhs', rhs' = invert_bin_exp at op e1 e2 t rhs in
    animate_exp_eq at lhs' rhs'
  (* All unary ops can be inverted. *)
  | UnE (op, t, exp) ->
    animate_exp_eq at exp (UnE (op, t, rhs) $$ rhs.at % exp.note)
  (* Unary tuples. Invert. *)
  | ProjE (e1, 0) ->
    let t' = reduce_typ !env e1.note in
    begin match t'.it with
    | VarT _ -> assert false
    | TupT [_] ->
      info "proj" at ("ProjE.0 on an ordinary singleton TupT type.");
      animate_exp_eq at e1 (TupE [rhs] $$ rhs.at % e1.note)
    | NumT _ ->
      (* It is possible that both e1.0 and e1 have the same type. *)
      info "proj" at ("Num type: " ^ string_of_typ t');
      animate_exp_eq at e1 (TupE [rhs] $$ rhs.at % e1.note)
    | _ -> E.throw (string_of_error at
                     ("Can't invert ProjE.0: " ^ string_of_exp e1 ^ " of type " ^ string_of_typ t'))
    end
  (* Unary constructors. Invert. *)
  | UncaseE (e1, mixop) ->
    (* Technically, need to check for the refinement when wrapping with a CaseE. *)
    let t' = reduce_typdef !env e1.note in
    begin match t'.it with
    (* Unary variant type, we can invert the UncaseE. *)
    | VariantT [_] ->
        animate_exp_eq at e1 (CaseE (mixop, rhs) $$ rhs.at % e1.note)
      (*
      (* FIXME(zilinc): The side-condition from the type definition.
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

and animate_if_prem at exp : prem list E.m =
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
    | true , false -> animate_exp_eq exp.at e2 e1
    | false, true  -> animate_exp_eq exp.at e1 e2
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
    animate_prem (IterPr ([IfPr exp' $ exp'.at], iterexp) $ at)
  | _ -> let unknowns = Set.diff fv_exp knowns in
         E.throw (string_of_error at (
                   "Can't animate if premise: " ^ string_of_exp exp ^ ".\n" ^
                   "  ▹ Unknowns: " ^ string_of_varset unknowns ^ "\n" ^
                   "  ▹ Knowns: " ^ string_of_varset knowns))


and animate_prem : prem -> prem list E.m = fun prem ->
  let open AnimState in
  let ( let* ) = E.( >>= ) in
  let* s = get () in
  let knowns = get_knowns s in
  let fv_prem = (free_prem false prem).varid in
  match prem.it with
  | RulePr (id, mixop, exp) ->
    info "rulepr" prem.at ("rule premise: " ^ id.it);
    animate_rule_prem prem.at id mixop exp
  | IfPr exp -> animate_if_prem prem.at exp
  | LetPr (e1, e2, ids) ->
    error prem.at ("Can't animate LetPr: " ^ string_of_prem prem)
  | ElsePr ->
    E.return [ prem ]
  | IterPr ([prem'], ((iter, xes) as iterexp)) ->
    (* The animation algorithm for IterPr goes as follows:
       Base case 1: (-- if exp)^iter where exp and iter are fully known.
         -- (if exp)^iter
         How do we generate Ocaml code from it?
         ▹ Need to look at the iterexp binding list to find the iterated expressions.
           TODO(zilinc): Does it have all the information to generate a parallel map_n function?
       Base case 2: (-- let v = rhs {v})^(i<N) {v <- v*} where N is known
         -- let `v*` = rhs^(i<N) {`v*`}
       Base case 3: (-- let v = rhs {v})^(i<N) {} where N is known
         It means that all v's must have the same value.
       Base case: (-- let v = rhs {v})^(i<N) where N is unknown
         Maybe can't animate in general.
       Inductive cases: (-- let v = rhs {v})^iter
         Reduce to base cases:
           For List:
           -- where N = |rhs| {N}
           -- animate (-- let v = rhs)^(i<N)
           For List1:
           additionally check -- if N >= 1
           For Opt:  (TODO(zilinc): does it need a special case to handle?)
           additionally check -- if N <= 1
       Inductive cases: (-- if exp)^iter. E.g.:
         animate (-- prem^(i<N){x <- X, y <- Y, i <- I})
         ~~>
         (animate prem)^(i<N){x <- X, y <- Y, i <- I}
         ~~>
         (prems')^(i<N){x <- X, y <- Y, i <- I}
         ~~>
         for prem' ∈ prems': (prem')^(i<N){???}
         ~~>  ;; pattern match on prem'
           prems' should be a series of
           -- let v = e {v} or -- if e (check)
           We then wrap each output with _^(i<N) { ... }. The iter-binding list
           should be { v <- v* }, plus those for the inputs.
           We can approximate it as all the free variables.
    *)
    begin match prem'.it, iter with
    | IfPr exp, _ when Set.is_empty (Set.diff fv_prem knowns) ->
      (* Base case 1 *)
      E.return [ prem ]
    | LetPr (lhs, rhs, binders), ListN (len, Some i) ->
      (* Because LetPr is animated, there should be only one free variable. *)
      let [v] = (free_exp false lhs).varid |> Set.elements in
      let fv_len = (free_exp false len).varid in
      let unknowns_len = Set.diff fv_len knowns in
      if Set.is_empty unknowns_len then
        match List.find_opt (fun (x, e) -> v = x.it) xes with
        | Some (v_id, v_star) ->
          (* Base case 2 *)
          let VarE v_star_id = v_star.it in
          (* Since [v] is unknown, whereas [rhs] is fully known, [v] cannot appear
             in [rhs]. We remove it from the binding list, which is for [rhs].
             Thus [xes'] should contain the exact entries for [rhs].
          *)
          let xes' = Lib.List.filter_not (fun (x, e) -> Il.Eq.eq_id v_id x) xes in
          let rhs' = IterE (rhs, (iter, xes')) $$ rhs.at % (IterT (rhs.note, iter) $ rhs.at) in
          animate_exp_eq prem.at v_star rhs'
        | None ->
          (* Base case 3 *)
          throw_log (string_of_error prem.at "IterPr Base case 3: not yet implemented: " ^ string_of_prem prem')
      else
        (* The iterator N is unknown *)
        E.throw (string_of_error prem.at ("IterPr has unknown iterator " ^ string_of_iter iter ^ "\n" ^
                                          "  ▹ unknowns: " ^ string_of_varset knowns))
    (* Inductive cases, where the body is -- let v = rhs but the iterator is not ^(i<N). *)
    | LetPr (_, _, binders), ListN(len, None) ->
      let i = fresh_id (Some "i") len.at in
      animate_prem (IterPr ([prem'], (ListN(len, Some i), xes)) $ prem.at)
    | LetPr (_, rhs, binders), _ ->
      let len_rhs = LenE rhs $$ rhs.at % mk_natT rhs.at in
      let len_v = fresh_id (Some "len") len_rhs.at in
      let len = VarE len_v $$ len_rhs.at % len_rhs.note in
      let* prems_len_v = animate_exp_eq len.at len len_rhs in
      let i = fresh_id (Some "i") len.at in
      let oprem_len = match iter with
      | List  -> None
      | Opt   -> Some (IfPr (CmpE (`LeOp, `NatT, len, mk_natE len.at 1) $$ len.at % (BoolT $ len.at)) $ prem.at)
      | List1 -> Some (IfPr (CmpE (`GeOp, `NatT, len, mk_natE len.at 1) $$ len.at % (BoolT $ len.at)) $ prem.at)
      | _ -> assert false
      in
      let* prems_len = match oprem_len with
      | None -> E.return []
      | Some prem_len -> animate_prem prem_len
      in
      let* prems' = animate_prem (IterPr ([prem'], (ListN(len, Some i), xes)) $ prem.at) in
      E.return (prems_len_v @ prems_len @ prems')
    (* Inductive case: arbitrary prem, arbitrary iter *)
    | _ ->
      (* Propagating knowns into the iteration. *)
      let iNs = match iter with
      | ListN(len, Some i) -> [(i, len)]
      | _ -> []
      in
      let knowns_inner = List.filter_map (fun (x, e) ->
        let fv_e = (free_exp false e).varid in
        let unknowns_e = Set.diff fv_e knowns in
        if Set.is_empty unknowns_e then Some x.it else None
      ) (xes @ iNs) |> Set.of_list in
      let s_body = { (init ()) with prems = [prem']; knowns = (Set.union knowns knowns_inner) } in
      let* (prems_body', s_body') = run_inner s_body (animate_prems' prem'.at) in
      (* Propagate knowns to the outside of the iterator. *)
      let knowns' = get_knowns s_body' in
      let knowns_outer = List.filter_map (fun (x, e) ->
        if Set.mem x.it knowns' then
          let fv_e = (free_exp false e).varid in
          let unknowns_e = Set.diff fv_e knowns' in
          Some (Set.elements unknowns_e)
        else
          None
      ) xes |> List.concat |> Set.of_list in
      let* () = update (add_knowns knowns_outer) in
      E.return [IterPr (prems_body', iterexp) $ prem.at]
    end
  | IterPr (prems, iterexp) -> todo "animate_prem"


(* The main loop. We handle the ordering of the premises in this function. *)
and animate_prems' at : prem list E.m =
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
                   animate_prems' at
                 (* has made some progress, enter next iteration *)
                 | true, _ ->
                   let* () = update (clr_progress >>> mv_to_prems) in
                   animate_prems' at
                 end
  (* continue with the current iteration *)
  | _ -> let ( let* ) = S.( >>= ) in
         E.exceptT (
           let* s = S.get () in
           let (prem, s') = pop_prems s in
           let* () = S.put s' in
           let* r = animate_prem prem |> E.run_exceptT in
           match r with
           | Error e ->
             (* Recover from failure. *)
             let* () = S.update (push_prems' prem >>> set_failure e) in
             animate_prems' at |> E.run_exceptT
           | Ok prems -> E.run_exceptT (
               let ( let* ) = E.( >>= ) in
               let* () = update set_progress in
               let* prems' = animate_prems' at in
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
and animate_prems at ins ous prems : prem list =
  animate_prems' at
  |> E.run_exceptT
  |> Fun.flip S.run_state ({ (AnimState.init ()) with prems; knowns = ins })
  |> function
     | (Error e, _) -> error at e
     | (Ok ps  , s) ->
       if Set.subset ous s.knowns then ps
       else error at ("Premises failed to compute all required output variables:\n" ^
                      "  ▹ knowns: " ^ string_of_varset s.knowns ^ "\n" ^
                      "  ▹ outs: " ^ string_of_varset ous)

let lift_otherwise_prem prems =
  let is_otherwise = function { it = ElsePr; _ } -> true | _ -> false in
  let (ow_pr, rest) = List.partition is_otherwise prems in
  ow_pr @ rest

let animate_rule_red at binds lhs rhs prems : clause' =
  let lhs_vars = (free_exp false lhs).varid in
  let rhs_vars = (free_exp false rhs).varid in
  let rule_binders = (bound_binds binds).varid in
  let prems_vars = List.map (fun prem -> (free_prem false prem).varid) prems in
  (* Input and output variables in the conclusion *)
  let in_vars = lhs_vars in
  let out_vars = Set.diff rhs_vars lhs_vars in
  let prems' = animate_prems at in_vars out_vars prems in
  DefD (binds, [ExpA lhs $ lhs.at], rhs, prems')

let animate_rule at (r : rule_clause) : clause =
  let (_, lhs, rhs, prems) = r in
  let clause' = animate_rule_red at [] lhs rhs prems in  (* TODO *)
  clause' $ at

let animate_rules at rs = List.map (animate_rule at) rs

let animate_clause (c: clause) : func_clause =
  let DefD (binds, args, exp, prems) = c.it in
  let n_args = List.length args in
  let ous = (free_exp false exp).varid in
  let blob = List.mapi (fun i arg -> match arg.it with
    | ExpA exp ->
      let v = fresh_id (Some ("a" ^ string_of_int i)) arg.at in
      let lhs = VarE v $$ v.at % exp.note in
      let p = IfPr (CmpE (`EqOp, `BoolT, lhs, exp) $$ exp.at % (BoolT $ exp.at)) $ arg.at in
      (ExpA lhs $ lhs.at, Some p, Some v)
    | _ -> (arg, None, None)
  ) args
  in
  let (args, o_prem_args, ovs) = Lib.List.unzip3 blob in
  let prems_args = List.filter_map Fun.id o_prem_args in
  let vs = List.filter_map Fun.id ovs in
  let ins = (free_list free_varid vs).varid in
  let prems' = animate_prems c.at ins ous (prems_args @ prems) |> lift_otherwise_prem in
  (DefD (binds, args, exp, prems')) $ c.at

let animate_clauses cs = List.map animate_clause cs


let animate_rule_def' at (rule_name, rel_id, rules) = (rel_id, animate_rules at rules)
let animate_rule_def (rdef: rule_def) : func_def = animate_rule_def' rdef.at rdef.it $ rdef.at

let animate_helper_def' (id, clauses, partial) = (id, animate_clauses clauses)
let animate_helper_def (hdef: helper_def) : func_def = animate_helper_def' hdef.it $ hdef.at

let animate_def (d: dl_def) = match d with
| RuleDef   rdef -> FuncDef (animate_rule_def   rdef)
| HelperDef hdef -> FuncDef (animate_helper_def hdef)


(* Merge all rules that have the same rel_id. *)
let rec merge_defs (defs: dl_def list) : dl_def list =
  let is_func = function
  | FuncDef _ -> true | _ -> false
  in
  let (funcs, rest) = List.partition is_func defs in

  let funcs' = match funcs with
  | [] -> []
  | f :: fs ->
    let func_id = function | FuncDef {it = (fid, _); _} -> fid | _ -> assert false
    in
    let fid0 = func_id f in
    let fs_same, fs_diff =
      List.partition (fun f -> func_id f = fid0) fs in
    let clauses = f :: fs_same |> List.concat_map (fun (FuncDef fdef) -> snd fdef.it) in
    let at = (f :: fs_same) |> List.map (fun (FuncDef fdef) -> fdef) |> List.map at |> over_region in
    let f' = FuncDef ((fid0, clauses) $ at) in
    f' :: merge_defs fs_diff
  in funcs' @ rest

(* Entry function *)
let animate (dl, il) =
  env := Il.Env.env_of_script il;
  dl |> List.map animate_def
     |> merge_defs
