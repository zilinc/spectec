open Il_util
open Construct
open Def
open Util
open Error
open Il.Ast
open Il.Print
open Source
open Printf
open Il2al.Free
module A = Al.Ast
module I = Backend_interpreter


(* Errors *)

let verbose : string list ref =
  ref ["match"; "eval"; "assign";  "iter"]

let error at msg = Error.error at "(Meta)Interpreter" msg
let error_np msg = error no_region msg

let string_of_error at msg = string_of_region at ^ " (Meta)Interpreter error:\n" ^ msg

let warn at msg = print_endline (string_of_region at ^ " (Meta)Interpreter warning:\n" ^ msg)

let info v at msg = if List.mem v !verbose || v = "" then
                      print_endline (string_of_region at ^ " (Meta)Interpreter info[" ^ v ^ "]:\n" ^ msg)
                    else
                      ()


(* Helper *)

let (--) start end_ : int list = List.init (end_ - start) (fun i -> start + i)

module OptMonad = struct
  type 'a m = 'a option
  let return a = Some a
  let fail     = None
  let ( >>= ) = Option.bind
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
end

open OptMonad

(* Environments *)

module VContext = struct
  module M = Map.Make(String)
  include M
  type t = exp M.t

  let dom ctx : Set.t = ctx |> M.bindings |> List.map fst |> Set.of_list
end


let dl : dl_def list ref = ref []
let il_env : Il.Env.t ref = ref Il.Env.empty


exception PatternMatchFailure

let fail_assign at lhs rhs msg =
  info "match" at ("Pattern-matching failed (" ^ msg ^ "):\n" ^
                   "  ▹ pattern: " ^ string_of_exp lhs ^ "\n" ^
                   "  ▹ value: " ^ string_of_exp rhs);
  raise PatternMatchFailure

(*
let rec infer_val' val_ : typ' = match val_ with
  | A.NumV num-> begin match num with
    | `Nat _  -> `NatT
    | `Int _  -> `IntT
    | `Rat _  -> `RatT
    | `Real _ -> `RealT
    end
    |> (fun t -> NumT t)
  | A.BoolV b   -> BoolT
  | A.TextV s   -> TextT
  | A.ListV arr when Array.length !arr > 0 -> IterT (infer_val (Array.get !arr 0), List)
  | A.ListV arr -> todo "ListV empty: can't infer"
  | A.StrV str  -> todo ""
  | A.CaseV (mop, vs) -> todo ""
  | A.OptV None -> todo "OptV: can't infer"
  | A.OptV (Some v) -> IterT (infer_val v, Opt)
  | A.TupV vs -> TupT (List.map (fun v ->
                         let t = infer_val v in
                         (VarE ("_" $ no_region) $$ no_region % t, infer_val v))
                      vs)
  | A.FnameV id -> todo ""
and infer_val val_ : typ = infer_val' val_ $ no_region


let text_to_mixop s : mixop = todo "text_to_mixop"

let rec val_to_exp' val_ : exp' = match val_ with
  | A.NumV num  -> NumE num
  | A.BoolV b   -> BoolE b
  | A.TextV s   -> TextE s
  | A.ListV arr -> todo ""
  | A.StrV str  -> StrE (List.map record_to_expfield str)
  | A.CaseV (mop, vs) -> CaseE (text_to_mixop mop, todo "val_to_exp': CaseV")
  | A.OptV ov   -> OptE (Option.map val_to_exp ov)
  | A.TupV vs   -> TupE (List.map val_to_exp vs)
  | A.FnameV id -> todo ""
and val_to_exp val_ : exp =
  let t = infer_val val_ in
  val_to_exp' val_ $$ no_region % t

and record_to_expfield (id, val_ref) : expfield =
  todo "record_to_expfield"
*)


let rec exp_to_val exp : A.value =
  match exp.it with
  | BoolE b  -> A.BoolV b
  | NumE num -> A.NumV num
  | TextE s  -> A.TextV s
  | TupE  es -> A.TupV  (List.map exp_to_val es)
  | ListE es -> A.ListV (List.map exp_to_val es |> Array.of_list |> ref)
  | OptE oe  -> A.OptV (Option.map exp_to_val oe)
  | CaseE (mixop, e) -> A.CaseV (string_of_mixop mixop, tup_to_val e)
  | SubE (e, _, _) | SupE (e, _, _) -> exp_to_val e
  | StrE fs -> A.StrV (List.map expfield_to_record fs)
  | _ -> error exp.at ("Expression is not in normal form: " ^ string_of_exp exp)

and expfield_to_record (atom, exp) : A.id * A.value ref =
  let id = string_of_atom atom in
  let val_  = exp_to_val exp in
  (id, ref val_)

and tup_to_val exp : A.value list =
  match exp.it with
  | TupE es -> List.map exp_to_val es
  | _       -> [exp_to_val exp]

let vctx_to_subst ctx : Il.Subst.subst =
  VContext.fold (fun var value subst ->
    Il.Subst.add_varid subst (var $ no_region) value
  ) ctx Il.Subst.empty

let rec assign ctx (lhs: exp) (rhs: exp) : VContext.t =
  info "assign" lhs.at ("Assign " ^ string_of_exp lhs ^ " to " ^ string_of_exp rhs);
  match lhs.it, rhs.it with
  | VarE name, _ ->
    VContext.add name.it rhs ctx
  | IterE ({ it = VarE x1; _ }, ((List|List1), [(x2, lhs')])), ListE _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs
  | IterE ({ it = VarE x1; _ }, (Opt, [x2, lhs'])), _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs
  | IterE (e, (Opt, xes)), _ ->
    assert false  (* Animation shouldn't output this. *)
  | IterE (e, ((ListN _|List|List1) as iter, xes)), ListE es ->
    let ctxs = List.map (assign VContext.empty e) es in

    (* Assign length variable *)
    let ctx' =
      match iter with
      | ListN (expr, None) ->
        let length = il_of_nat (List.length es) in
        assign ctx expr length
      | ListN _ ->
        fail_assign lhs.at lhs rhs ("invalid assignment: iter with index cannot be an assignment target")
      | _ -> ctx
    in

    List.fold_left (fun ctx (x, e) ->
      let vs = List.map (VContext.find x.it) ctxs in
      let v = match iter with
      | Opt -> optE e.note (List.nth_opt vs 0)
      | _   -> listE e.note vs
      in
      assign ctx e v
    ) ctx' xes
  | TupE lhs_s, TupE rhs_s
    when List.length lhs_s = List.length rhs_s ->
    List.fold_left2 assign ctx lhs_s rhs_s
  | CaseE (lhs_tag, lhs_s), CaseE (rhs_tag, rhs_s) ->
    begin match lhs_s.it, rhs_s.it with
    | TupE lhs_s', TupE rhs_s' ->
      if Il.Eq.eq_mixop lhs_tag rhs_tag && List.length lhs_s' = List.length rhs_s' then
        List.fold_left2 assign ctx lhs_s' rhs_s'
      else
        fail_assign lhs.at lhs rhs "tag or payload doesn't match"
    | _ -> fail_assign lhs.at lhs rhs "not a TupE inside a CaseE"
    end
  | OptE (Some lhs'), OptE (Some rhs') -> assign ctx lhs' rhs'
  | CvtE (e1, nt, _), NumE n ->
    (match Xl.Num.cvt nt n with
    | Some n' -> assign ctx e1 (mk_expr rhs.at (NumT nt $ rhs.at) (NumE n'))
    | None -> fail_assign lhs.at lhs rhs ("inverse conversion not defined for " ^ string_of_exp rhs)
    )
  | _, _ -> fail_assign lhs.at lhs rhs "invalid pattern"


let rec eval_exp ctx exp : exp =
  let subst = vctx_to_subst ctx in
  let exp' = Il.Subst.subst_exp subst exp in
  match exp'.it with
  (* NOTE: We assume function calls are at the root of the AST. *)
  | CallE (fid, args) ->
    let args' = List.map (Il.Eval.reduce_arg !il_env) args in
    call_func fid.it args'
  | _ -> Il.Eval.reduce_exp !il_env exp'

and eval_prem ctx prem : VContext.t OptMonad.m =
  info "match" prem.at ("Match premise: " ^ string_of_prem prem);
  match prem.it with
  | LetPr (lhs, rhs, _vs) ->
    let rhs' = eval_exp ctx rhs in
    return (assign ctx lhs rhs')
  | IfPr e ->
    let b = eval_exp ctx e in
    if b.it = BoolE true then return ctx
    else
      (info "match" prem.at ("If premise failed."); fail)
  | IterPr (prems, (iter, xes)) ->
    (* Work out which variables are inflow and which are outflow. *)
    let in_binds, out_binds = List.fold_right (fun (x, e) (ins, ous) ->
      let fv_e = (free_exp false e).varid in
      if Set.subset fv_e (VContext.dom ctx) then
        (x, e)::ins, ous
      else
        ins, (x, e)::ous
    ) xes ([], []) in
    begin match iter with
    | ListN (n, Some i) ->
      let* n' = begin match (eval_exp ctx n).it with
      | NumE (`Nat n') -> return (Z.to_int n')
      | n' -> (info "eval" n.at ("Expression " ^ string_of_exp n ^ " ~> " ^
                                 string_of_exp (n' $> n) ^ " is not a nat.");
               fail)
      end in
      info "iter" n.at ("Iter length n' = " ^ string_of_int n');
      let il_env0 = !il_env in
      (* Extend il_env with "local" variables in the iteration *)
      List.iter (fun (x, e) ->
        match e.it with
        | VarE x_star ->
          let t_star = Il.Env.find_var !il_env x_star in
          let t = Il_util.as_iter_typ !il_env t_star in
          il_env := Il.Env.(bind_var !il_env x t);
        | _ -> assert false
      ) (in_binds @ out_binds);
      info "iter" prem.at ("in-binds are: " ^ string_of_iterexp (iter, in_binds) ^ "\n" ^
                            "out-binds are: " ^ string_of_iterexp (iter, out_binds));
      (* Initialise the out-vars, so that even when n' = 0 they are still assigned to `eps`. *)
      let ctx' = List.fold_left (fun ctx (x, e) ->
        match e.it with
        | VarE x_star ->
          let vx_star = ListE [] $$ no_region % e.note in
          info "iter" prem.at ("Initialise " ^ x_star.it ^ " to " ^ string_of_exp vx_star);
          VContext.add x_star.it vx_star ctx
        | _ -> assert false
      ) ctx out_binds in
      (* Run the loop *)
      let* ctx'' = foldlM (fun ctx idx ->
        let lctxr = ref ctx in
        lctxr := VContext.add i.it (mk_nat idx) !lctxr;
        (* In-flow *)
        List.iter (fun (x, e) ->
          let t = Il.Env.find_var !il_env x in
          let e' = eval_exp ctx (IdxE (e, mk_nat idx) $$ e.at % t) in
          lctxr := VContext.add x.it e' !lctxr
        ) in_binds;
        let* lctx = eval_prems !lctxr prems in
        lctxr := lctx;
        (* Out-flow *)
        List.iter (fun (x, e) ->
          match e.it with
          | VarE x_star ->
            let vx = VContext.find x.it !lctxr in
            let opt_vx_star = VContext.find_opt x_star.it !lctxr in
            begin match opt_vx_star with
            | Some vx_star ->
              begin match vx_star.it with
              | ListE es -> let vx_star' = ListE (es @ [vx]) $> vx_star in
                            info "iter" prem.at ("Outflow: " ^ x_star.it ^ " := " ^ string_of_exp vx_star');
                            lctxr := VContext.add x_star.it vx_star' !lctxr
              | _ -> assert false
              end
            | _ -> assert false
            end
          | _ -> assert false
        ) out_binds;
        return !lctxr
      ) ctx' (0 -- n') in
      il_env := il_env0;  (* Resume old environment *)
      return ctx''
    | ListN (n, None) -> todo "eval_prem: IterPr ListN(_, None)"
    | List | List1 -> todo "eval_prem: IterPr List|List1"
    | Opt -> todo "eval_prem: IterPr Opt"
    end
  | _ -> assert false

and eval_prems ctx prems : VContext.t OptMonad.m =
  match prems with
  | [] -> return ctx
  | prem :: prems ->
    let* ctx = eval_prem ctx prem in
    let* ctx = eval_prems ctx prems in
    return ctx

and match_arg at (pat: arg) (arg: arg) : VContext.t option =
  match pat.it, arg.it with
  | TypA ptyp , TypA _    -> todo "match_arg TypA"
  | ExpA pexp , ExpA aexp -> (try Some (assign VContext.empty pexp aexp) with PatternMatchFailure -> None)
  | DefA pid  , DefA _    -> todo "match_arg DefA"
  | GramA psym, GramA _   -> todo "match_arg GramA"
  | _ -> (info "match" at ("Wrong argument sort: " ^ string_of_arg arg ^ " doesn't match pattern " ^ string_of_arg pat); None)


and match_args at pargs args : VContext.t option =
  match pargs, args with
  | [], [] -> return VContext.empty
  | parg::pargs', arg::args' ->
    let* vctx = match_arg at parg arg in
    let* vctx' = match_args at pargs' args' in
    return (VContext.union (fun k _ _ -> error at ("Duplicate variable `" ^ k ^ "`")) vctx vctx')

and match_clause at (fname: string) (clauses: clause list) (args: arg list) : exp =
  info "match" at ("Match_clause: `" ^ fname ^ "`");
  match clauses with
  | [] -> error at ("No function clause matches the input arguments in function `" ^ fname ^ "`")
  | cl :: cls ->
    let DefD (binds, pargs, exp, prems) = cl.it in
    let env_binds = Animate.env_of_binds binds il_env in
    il_env := Il.Env.env_merge !il_env !env_binds;
    assert (List.length pargs = List.length args);
    match match_args cl.at pargs args with
    | Some vctx ->
      begin match eval_prems vctx prems with
      | Some ctx -> eval_exp ctx exp
      | None     -> match_clause at fname cls args
      end
    | None -> match_clause at fname cls args


and eval_func name func_def args : exp =
  let (_, params, typ, fcs, _) = func_def.it in
  match_clause no_region name fcs args


and call_func name args : exp =
  let builtin_name, is_builtin =
    match Il.Env.find_func_hint !il_env name "builtin" with
    | None -> name, false
    | Some hint ->
      match hint.hintexp.it with
      | SeqE [] -> name, true         (* hint(builtin) *)
      | TextE fname -> fname, true    (* hint(builtin "g") *)
      | _ -> failwith (sprintf "ill-formed builtin hint for definition `%s`." name)
  in
  (* Function *)
  match Def.find_dl_func_def name !dl with
  | Some fdef when not is_builtin -> eval_func name fdef args
  (* Numerics *)
  | None when I.Numerics.mem builtin_name -> (
    if not is_builtin then
      warn no_region (sprintf "Numeric function `%s` is not defined in source, consider adding a hint(builtin)." name);
    (* Some (I.Numerics.call_numerics builtin_name args) *)
    error no_region "call_func: Can't call built-in functions for now; not yet implemented."
  )
  (* Relation *)
  | None when Relation.mem name -> Relation.call_func name args
  | None -> raise (I.Exception.UnknownFunc ("There is no function named: " ^ name))



(* Wasm interpreter entry *)

let instantiate (args: arg list) : exp = call_func "instantiate" args

let invoke (args: arg list) : exp = call_func "invoke" args
