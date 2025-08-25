open Def
open Util
open Error
open Il.Ast
open Il.Print
open Source
open Printf
open Al.Al_util
module A = Al.Ast
module I = Backend_interpreter


(* Errors *)

let verbose : string list ref =
  ref ["interpreter"]

let error at msg = Error.error at "(Meta)Interpreter" msg
let error_np msg = error no_region msg

let string_of_error at msg = string_of_region at ^ " (Meta)Interpreter error:\n" ^ msg

let warn at msg = print_endline (string_of_region at ^ " (Meta)Interpreter warning:\n" ^ msg)

let info v at msg = if List.mem v !verbose || v = "" then
                      print_endline (string_of_region at ^ " (Meta)Interpreter info[" ^ v ^ "]:\n" ^ msg)
                    else
                      ()


(* Environments *)

module VCtx = Map.Make(String)
type vcontext = A.value VCtx.t

let dl : dl_def list ref = ref []
let il_env : Il.Env.t ref = ref Il.Env.empty


let ( let* ) = Option.bind

exception PatternMatchFailure

let fail_assign at lhs rhs msg =
  error at ("Pattern-matching failed (" ^ msg ^ "):\n" ^
            "  ▹ pattern: " ^ string_of_exp lhs ^ "\n" ^
            "  ▹ value: " ^ Al.Print.string_of_value rhs)

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
  VCtx.fold (fun var value subst ->
    let exp = val_to_exp value in
    Il.Subst.add_varid subst (var $ no_region) exp
  ) ctx Il.Subst.empty

let rec assign ctx (lhs: exp) (rhs: A.value) : vcontext =
  match lhs.it, rhs with
  | VarE name, _ -> VCtx.add name.it rhs ctx
  | IterE ({ it = VarE x1; _ }, ((List|List1), [(x2, lhs')])), ListV _ when x1 = x2 ->
    assign ctx lhs' rhs
  | IterE (e, (iter, xes)), _ ->
    let vs = unwrap_seqv_to_list rhs in
    let ctxs = List.map (assign VCtx.empty e) vs in

    (* Assign length variable *)
    let ctx' =
      match iter with
      | ListN (expr, None) ->
        let length = natV_of_int (List.length vs) in
        assign ctx expr length
      | ListN _ ->
        fail_assign lhs.at lhs rhs ("invalid assignment: iter with index cannot be an assignment target")
      | _ -> ctx
    in

    List.fold_left (fun ctx (x, e) ->
      let vs = List.map (VCtx.find x.it) ctxs in
      let v = match iter with
      | Opt -> optV (List.nth_opt vs 0)
      | _   -> listV_of_list vs
      in
      assign ctx e v
    ) ctx' xes
  | TupE lhs_s, TupV rhs_s
    when List.length lhs_s = List.length rhs_s ->
    List.fold_left2 assign ctx lhs_s rhs_s
  (*
  | ListE lhs_s, ListV rhs_s
    when List.length lhs_s = Array.length !rhs_s ->
    List.fold_left2 assign ctx lhs_s (Array.to_list !rhs_s)
  *)
  | CaseE (op, lhs_s), CaseV (rhs_tag, rhs_s) ->
    begin match lhs_s.it with
    | TupE lhs_s' when List.length lhs_s' = List.length rhs_s ->
      (match get_atom op with
      | Some lhs_tag when (Al.Print.string_of_atom lhs_tag) = rhs_tag ->
        List.fold_left2 assign ctx lhs_s' rhs_s
      | None when "" = rhs_tag ->
        List.fold_left2 assign ctx lhs_s' rhs_s
      | _ -> fail_assign lhs.at lhs rhs "constructor doesn't match"
      )
    | _ -> fail_assign lhs.at lhs rhs "not a TupE inside a CaseE"
    end
  | OptE (Some lhs'), OptV (Some rhs') -> assign ctx lhs' rhs'
  | CvtE (e1, nt, _), NumV n ->
    (match Xl.Num.cvt nt n with
    | Some n' -> assign ctx e1 (NumV n')
    | None -> fail_assign lhs.at lhs rhs ("inverse conversion not defined for " ^ Al.Print.string_of_value (NumV n))
    )
  | _, _ -> fail_assign lhs.at lhs rhs "invalid pattern"


let eval_exp ctx exp : A.value =
  let subst = vctx_to_subst ctx in
  let exp' = Il.Subst.subst_exp subst exp in
  let exp'' = Il.Eval.reduce_exp !il_env exp' in
  exp_to_val exp''

let eval_prem ctx prem : vcontext option =
  match prem.it with
  | LetPr (lhs, rhs, _vs) ->
    let rhs' = eval_exp ctx rhs in
    Some (assign ctx lhs rhs')
  | IfPr e ->
    let b = eval_exp ctx e in
    if b = BoolV true then Some ctx else None
  | IterPr (prems, iter) -> todo "eval_prem: IterPr"
  | _ -> assert false

let rec eval_prems ctx prems : vcontext option =
  match prems with
  | [] -> Some ctx
  | prem :: prems ->
    let* ctx = eval_prem ctx prem in
    let* ctx = eval_prems ctx prems in
    Some ctx

let match_arg at (parg: arg) (arg: A.value) : vcontext option =
  match parg.it with
  | TypA typ  -> todo "match_arg TypA"
  | ExpA exp  -> (try Some (assign VCtx.empty exp arg) with PatternMatchFailure -> None)
  | DefA id   -> todo "match_arg DefA"
  | GramA sym -> todo "match_arg GramA"


let rec match_args at pargs args : vcontext option =
  match pargs, args with
  | [], [] -> Some VCtx.empty
  | parg::pargs', arg::args' ->
    let* vctx = match_arg at parg arg in
    let* vctx' = match_args at pargs' args' in
    Some (VCtx.union (fun k _ _ -> error at ("Duplicate variable `" ^ k ^ "`")) vctx vctx')

let rec match_clause at (fname: string) (clauses: clause list) (args: A.value list) : A.value =
  info "interpreter" at ("match_clause: `" ^ fname ^ "`.");
  match clauses with
  | [] -> error at ("No function clause matches the input arguments in function " ^ fname)
  | cl :: cls ->
    let DefD (_, pargs, exp, prems) = cl.it in
    assert (List.length pargs = List.length args);
    match match_args cl.at pargs args with
    | Some vctx ->
      begin match eval_prems vctx prems with
      | Some ctx -> eval_exp ctx exp
      | None     -> match_clause at fname cls args
      end
    | None -> match_clause at fname cls args


let eval_func name func_def args : A.value =
  let (_, params, typ, fcs, _) = func_def.it in
  match_clause no_region name fcs args


let call_func name args : A.value option =
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
  | Some fdef when not is_builtin ->
    Some (eval_func name fdef args)
  (* Numerics *)
  | None when I.Numerics.mem builtin_name -> (
    if not is_builtin then
      warn no_region (sprintf "Numeric function `%s` is not defined in source, consider adding a hint(builtin)." name);
    Some (I.Numerics.call_numerics builtin_name args)
  )
  (* Relation *)
  | None when I.Relation.mem name -> (
    raise (I.Exception.UnknownFunc (sprintf "Relation %s doesn't have an animated function" name))
    (*
    match Il.Env.find_opt_rel !il_env (name $ no_region) with
    | Some rdef ->
      [create_context name args]
      |> run
      |> AlContext.get_return_value
    else
      Some (Relation.call_func name args)
    *)
  )
  | None ->
    raise (I.Exception.UnknownFunc ("There is no function named: " ^ name))



(* Wasm interpreter entry *)

let instantiate (args: A.value list) : A.value =
  (* WasmContext.init_context (); *)
  match call_func "instantiate" args with
  | Some module_inst -> module_inst
  | None -> failwith "Instantiation doesn't return module instance"

let invoke (args: A.value list) : A.value =
  (* WasmContext.init_context (); *)
  match call_func "invoke" args with
  | Some v -> v
  | None -> failwith "Invocation doesn't return any values"


