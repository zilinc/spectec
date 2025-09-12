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
  ref ["log"; "match"; "eval"; "assign"; "iter"]

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
  let ( <$> ) = Option.map
  let ( <&> ) = Fun.flip ( <$> )
  let ( >>= ) = Option.bind
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let mapM f = Fun.flip (List.fold_right (fun a m -> let* x = f a in
                                                     let* xs = m in
                                                     return (x::xs)))
                        (return [])

  let mapiM f xs =
    let rec mapiM' f i = function
    | [] -> return []
    | x::xs -> let* x'  = f i x in
               let* xs' = mapiM' f (i+1) xs in
               return (x'::xs')
    in
    mapiM' f 0 xs

  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs

  let rec iterM f = function
    | [] -> ()
    | x::xs -> (match f x with
               | None -> ()
               | Some _ -> iterM f xs
               )
end

open OptMonad

let fail_log at msg = info "log" at msg; fail

let fail_log_exp etyp exp onotes =
  let notes = match onotes with
  | None     -> ""
  | Some msg -> "\n  ▹ " ^ msg
  in
  fail_log exp.at (etyp ^ " can't evaluate: " ^ string_of_exp exp ^ notes)

let string_of_exp exp = 
  let cap = 100 in
  let s = Il.Print.string_of_exp exp in
  if String.length s >= cap then String.sub s 0 cap ^ "... (too long)" else s

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


let as_opt_exp e =
  match e.it with
  | OptE eo -> eo
  | _ -> failwith "as_opt_exp"

let as_list_exp e =
  match e.it with
  | ListE es -> es
  | _ -> failwith "as_list_exp"

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


let rec eval_exp ctx exp : exp OptMonad.m =
  let open Xl in
  match exp.it with
  | VarE v -> (match VContext.find_opt v.it ctx with
              | Some v' -> Some v'
              | None -> (fail_log exp.at (sprintf "Variable `%s` is not in the value context.\n  ▹ vctx: %s" v.it
                                            (string_of_varset (VContext.dom ctx))))
              )
  | BoolE _ | NumE _ | TextE _ -> return exp
  | UnE (op, _, e1) ->
    let* e1' = eval_exp ctx e1 in
    (match op, e1'.it with
    | #Bool.unop as op', BoolE b1 -> BoolE (Bool.un op' b1) $> exp |> return
    | #Num.unop  as op', NumE  n1 -> let* n = Num.un op' n1 in NumE n $> exp |> return
    | _ -> fail_log_exp "Unary expression" exp None
    )
  | BinE (op, ot, e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match op with
    | #Bool.binop as op' ->
      Bool.bin_partial op' e1'.it e2'.it of_bool_exp to_bool_exp <&> (Fun.flip ($>) exp)
    | #Xl.Num.binop as op' ->
      Num.bin_partial op' e1'.it e2'.it of_num_exp to_num_exp <&> (Fun.flip ($>) exp)
    )
  | CmpE (op, ot, e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match op, e1'.it, e2'.it with
    | `EqOp, _, _ when Il.Eq.eq_exp e1' e2' -> BoolE true  |> return
    | `NeOp, _, _ when Il.Eq.eq_exp e1' e2' -> BoolE false |> return
    | `EqOp, _, _ when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE false |> return
    | `NeOp, _, _ when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE true  |> return
    | #Num.cmpop as op', NumE n1, NumE n2 -> let* b = Num.cmp op' n1 n2 in BoolE b |> return
    | _ -> fail_log_exp "Comparison expression" exp None
    ) <&> (Fun.flip ($>) exp)
  | IdxE (e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es, NumE (`Nat i) when i < Z.of_int (List.length es) -> List.nth es (Z.to_int i) |> return
    | _ -> fail_log_exp "Indexing expression" exp None
    )
  | SliceE (e1, e2, e3) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    let* e3' = eval_exp ctx e3 in
    (match e1'.it, e2'.it, e3'.it with
    | ListE es, NumE (`Nat i), NumE (`Nat n) when Z.(i + n) < Z.of_int (List.length es) ->
      ListE (Lib.List.take (Z.to_int n) (Lib.List.drop (Z.to_int i) es)) $> exp |> return
    | _ -> fail_log_exp "Slicing expression" exp None
    )
  | UpdE (e1, p, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    eval_path ctx e1' p
      (fun e' p' ->
        if p'.it = RootP
        then return e2'
        else fail_log_exp "Sequence update expression" exp None
      )
  | ExtE (e1, p, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    eval_path ctx e1' p
      (fun e' p' ->
        if p'.it = RootP
        then eval_exp ctx (CatE (e', e2') $> e')
        else fail_log_exp "Sequence extension expression" exp None
      )
  | StrE efs -> let* efs' = mapM (eval_expfield ctx) efs in StrE efs' $> exp |> return
  | DotE (e1, atom) ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | StrE efs -> snd (List.find (fun (atomN, _) -> Atom.eq atomN atom) efs) |> return
    | _ -> fail_log_exp "Struct dot expression" exp None
    )
  | CompE (e1, e2) ->
    (* TODO(4, rossberg): avoid overlap with CatE? *)
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es1, ListE es2 -> ListE (es1 @ es2) |> return
    | OptE None, OptE _ -> return e2'.it
    | OptE _, OptE None -> return e1'.it
    | StrE efs1, StrE efs2 ->
      let merge (atom1, e1) (atom2, e2) =
        assert (Atom.eq atom1 atom2);
        let* e12' = eval_exp ctx (CompE (e1, e2) $> e1) in
        return (atom1, e12')
      in
      let* efs12' = mapM (Lib.Fun.uncurry merge) (List.combine efs1 efs2) in
      return (StrE efs12')
    | _ -> fail_log_exp "Sequence composition expression" exp None
    ) <&> (Fun.flip ($>) exp)
  | MemE (e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e2'.it with
    | OptE None -> BoolE false |> return
    | OptE (Some e2') when Il.Eq.eq_exp e1' e2' -> BoolE true |> return
    | OptE (Some e2') when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE false |> return
    | ListE [] -> BoolE false |> return
    | ListE es2' when List.exists (Il.Eq.eq_exp e1') es2' -> BoolE true |> return
    | ListE es2' when Il.Eval.is_normal_exp e1' && List.for_all Il.Eval.is_normal_exp es2' -> BoolE false |> return
    | _ -> fail_log_exp "Membership expression" exp None
    ) <&> (Fun.flip ($>) exp)
  | LenE e1 ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | ListE es -> NumE (`Nat (Z.of_int (List.length es))) $> exp |> return
    | _ -> fail_log_exp "Sequence length expression" exp None
    )
  | TupE es -> let* es' = mapM (eval_exp ctx) es in TupE es' $> exp |> return
  | CallE (fid, args) ->
    let* args' = mapM (eval_arg ctx) args in
    call_func fid.it args'
  | IterE (e1, iterexp) ->
    let* (iter', xes') as iterexp' = eval_iterexp ctx iterexp in
    let ids, es' = List.split xes' in
    if iter' <= List1 && es' = [] then
      fail_log_exp "Iterated expression" exp (Some "Inadequate information about the iteration scheme.")
    else
      (match iter' with
      | Opt ->
        let eos' = List.map as_opt_exp es' in
        if List.for_all Option.is_none eos' then
          OptE None $> exp |> return
        else if List.for_all Option.is_some eos' then
          let es1' = List.map Option.get eos' in
          let ctx' = List.fold_left2 (fun c k v -> VContext.add k.it v c) ctx ids es1' in
          eval_exp ctx' e1
        else
          fail
      | List | List1 ->
        let n = List.length (as_list_exp (List.hd es')) in
        if iter' = List || n >= 1 then
          let en = NumE (`Nat (Z.of_int n)) $$ exp.at % (NumT `NatT $ exp.at) in
          eval_exp ctx (IterE (e1, (ListN (en, None), xes')) $> exp)
        else
          fail_log_exp "Iterated expression" exp (Some "Using + iterator but sequence length is 0")
      | ListN ({it = NumE (`Nat n'); _}, ido) ->
        let ess' = List.map as_list_exp es' in
        let ns = List.map List.length ess' in
        let n = Z.to_int n' in
        if List.for_all ((=) n) ns then
          let* e1s' = mapM (fun i ->
            let esI' = List.map (fun es -> List.nth es i) ess' in
            let ctx' = List.fold_left2 (fun c k v -> VContext.add k.it v c) ctx ids esI' in
            let ctx'' =
              Option.fold ido ~none:ctx' ~some:(fun id ->
                let en = NumE (`Nat (Z.of_int i)) $$ id.at % (NumT `NatT $ id.at) in
                VContext.add id.it en ctx'
              )
            in eval_exp ctx'' e1
          ) (0 -- n)
          in
          ListE e1s' $> exp |> return
        else
          fail_log_exp "Iterated expression" exp (Some "Inflow sequences don't agree on the length")
      | ListN _ -> fail_log_exp "Iterated expression" exp None
      )
  | ProjE (e1, i) ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | TupE es -> List.nth es i |> return
    | _ -> fail_log_exp "Tuple projection expression" exp None
    )
  | UncaseE (e1, mixop) ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | CaseE (mixop', e11') when Il.Eq.eq_mixop mixop mixop' -> return e11'
    | _ -> fail_log_exp "Constructor payload extraction expression" exp None
    )
  | OptE eo -> let* eo' = Option.map (eval_exp ctx) eo in OptE eo' $> exp |> return
  | TheE e1 ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | OptE (Some e11) -> return e11
    | _ -> fail_log_exp "THE expression" exp None
    )
  | ListE es -> let* es' = mapM (eval_exp ctx) es in ListE es' $> exp |> return
  | LiftE e1 ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | OptE None -> ListE [] |> return
    | OptE (Some e11') -> ListE [e11'] |> return
    | _ -> fail_log_exp "Option lifting expression" exp None
    ) <&> (Fun.flip ($>) exp)
  | CatE (e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es1, ListE es2 -> ListE (es1 @ es2) |> return
    | OptE None, OptE _ -> return e2'.it
    | OptE _, OptE None -> return e1'.it
    | _ -> fail_log_exp "Sequence concatenation expression" exp None
    ) <&> (Fun.flip ($>) exp)
  | CaseE (op, e1) -> let* e1' = eval_exp ctx e1 in CaseE (op, e1') $> exp |> return
  | CvtE (e1, _nt1, nt2) ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | NumE n -> let* n' = Num.cvt nt2 n in NumE n' $> exp |> return
    | _ -> fail_log_exp "Numeric type conversion" exp None
    )
  | SubE (e1, t1, t2) when Il.Eval.equiv_typ !il_env t1 t2 -> eval_exp ctx e1
  | SubE (e1, t1, t2) ->
    let* e1' = eval_exp ctx e1 in
    let t1' = Il.Eval.reduce_typ !il_env t1 in
    let t2' = Il.Eval.reduce_typ !il_env t2 in
    (match e1'.it with
    | SubE (e11', t11', _t12') -> eval_exp ctx (SubE (e11', t11', t2') $> exp)
    | TupE es' ->
      (match t1.it, t2.it with
      | TupT ets1, TupT ets2 ->
        let* (_, _, res') =
          List.fold_left2 (fun opt eI ((e1I, t1I), (e2I, t2I)) ->
            let* (s1, s2, res') = opt in
            let t1I' = Il.Subst.subst_typ s1 t1I in
            let t2I' = Il.Subst.subst_typ s2 t2I in
            let* e1I' = eval_exp ctx (Il.Subst.subst_exp s1 e1I) in
            let* e2I' = eval_exp ctx (Il.Subst.subst_exp s2 e2I) in
            let* s1' = try Il.Eval.match_exp !il_env s1 eI e1I' with Il.Eval.Irred -> None in
            let* s2' = try Il.Eval.match_exp !il_env s2 eI e2I' with Il.Eval.Irred -> None in
            let* eI' = eval_exp ctx (SubE (eI, t1I', t2I') $$ eI.at % t2I') in
            Some (s1', s2', eI'::res')
          ) (Some (Il.Subst.empty, Il.Subst.empty, [])) es' (List.combine ets1 ets2)
        in
        TupE (List.rev res') $> exp |> return
      | _ -> fail
      )
    | _ -> fail
    )
  (* TODO(zilinc): check SupE. *)
  | SupE (e1, t1, t2) when Il.Eval.equiv_typ !il_env t1 t2 -> eval_exp ctx e1
  | SupE (e1, t1, t2) ->
    let* e1' = eval_exp ctx e1 in
    let t1' = Il.Eval.reduce_typ !il_env t1 in
    let t2' = Il.Eval.reduce_typ !il_env t2 in
    (match e1'.it with
    | SupE (e11', t11', _t12') -> eval_exp ctx (SupE (e11', t11', t2') $> exp)
    | TupE es' ->
      (match t1.it, t2.it with
      | TupT ets1, TupT ets2 ->
        let* (_, _, res') = 
          List.fold_left2 (fun opt eI ((e1I, t1I), (e2I, t2I)) ->
            let* (s1, s2, res') = opt in
            let t1I' = Il.Subst.subst_typ s1 t1I in
            let t2I' = Il.Subst.subst_typ s2 t2I in
            let* e1I' = eval_exp ctx (Il.Subst.subst_exp s1 e1I) in
            let* e2I' = eval_exp ctx (Il.Subst.subst_exp s2 e2I) in
            let* s1' = try Il.Eval.match_exp !il_env s1 eI e1I' with Il.Eval.Irred -> None in
            let* s2' = try Il.Eval.match_exp !il_env s2 eI e2I' with Il.Eval.Irred -> None in
            let* eI' = eval_exp ctx (SupE (eI, t1I', t2I') $$ eI.at % t2I') in
            Some (s1', s2', eI'::res')
          ) (Some (Il.Subst.empty, Il.Subst.empty, [])) es' (List.combine ets1 ets2)
        in
        TupE (List.rev res') $> exp |> return
      | _ -> fail
      )
    | _ -> fail
    )

and eval_iter ctx = function
  | ListN (e, ido) -> let* e' = eval_exp ctx e in ListN (e', ido) |> return
  | iter -> return iter

and eval_iterexp ctx (iter, xes) : iterexp OptMonad.m =
  let* iter' = eval_iter ctx iter in
  let* xes' = mapM (fun (id, e) -> let* e' = eval_exp ctx e in return (id, e')) xes in
  return (iter', xes')

and eval_expfield ctx (atom, e) : expfield OptMonad.m =
  let* e' = eval_exp ctx e in return (atom, e')

and eval_path ctx e p (f: exp -> path -> exp OptMonad.m) : exp OptMonad.m =
  match p.it with
  | RootP -> f e p
  | IdxP (p1, e1) ->
    let* e1' = eval_exp ctx e1 in
    let f' e' p1' =
      match e'.it, e1'.it with
      | ListE es, NumE (`Nat i) when i < Z.of_int (List.length es) ->
        let* es' = mapiM (fun j eJ -> if Z.of_int j = i then f eJ p1' else return eJ) es in
        ListE es' $> e' |> return
      | _ -> fail_log e.at ("Index path failed to evaluate:\n" ^
                            "  ▹ e: " ^ string_of_exp e ^ "\n" ^
                            "  ▹ p: " ^ string_of_path p)
    in
    eval_path ctx e p1 f'
  | SliceP (p1, e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    let f' e' p1' =
      match e'.it, e1'.it, e2'.it with
      | ListE es, NumE (`Nat i), NumE (`Nat n) when Z.(i + n) < Z.of_int (List.length es) ->
        let e1' = ListE Lib.List.(take (Z.to_int i) es) $> e' in
        let e2' = ListE Lib.List.(take (Z.to_int n) (drop (Z.to_int i) es)) $> e' in
        let e3' = ListE Lib.List.(drop Z.(to_int (i + n)) es) $> e' in
        let* e2'' = f e2' p1' in
        eval_exp ctx (CatE (e1', CatE (e2'', e3') $> e') $> e')
      | _ -> fail_log e.at ("Slice path failed to evaluate:\n" ^
                            "  ▹ e: " ^ string_of_exp e ^ "\n" ^
                            "  ▹ p: " ^ string_of_path p)
    in
    eval_path ctx e p1 f'
  | DotP (p1, atom) ->
    let f' e' p1' =
      match e'.it with
      | StrE efs ->
        let* efs' = mapM (fun (atomI, eI) ->
          if Il.Eq.eq_atom atomI atom
          then let* eI' = f eI p1' in return (atomI, eI')
          else return (atomI, eI)
        ) efs in
        StrE efs' $> e' |> return
      | _ -> fail_log e.at ("Dot path failed to evaluate:\n" ^
                            "  ▹ e: " ^ string_of_exp e ^ "\n" ^
                            "  ▹ p: " ^ string_of_path p)
    in
    eval_path ctx e p1 f'

and eval_arg ctx a : arg OptMonad.m =
  match a.it with
  | ExpA  e  -> let* e' = eval_exp ctx e in ExpA e' $ a.at |> return
  | TypA _t  -> return a  (* types are reduced on demand *)
  | DefA _id -> return a
  | GramA _g -> return a

and eval_prem ctx prem : VContext.t OptMonad.m =
  info "match" prem.at ("Match premise: " ^ string_of_prem prem);
  match prem.it with
  | LetPr (lhs, rhs, _vs) ->
    let* rhs' = eval_exp ctx rhs in
    return (assign ctx lhs rhs')
  | IfPr e ->
    let* b = eval_exp ctx e in
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
      let* n' = eval_exp ctx n in
      let* n'' = begin match n'.it with
      | NumE (`Nat n'') -> return (Z.to_int n'')
      | n'' -> (info "eval" n.at ("Expression " ^ string_of_exp n ^ " ~> " ^
                                  string_of_exp (n'' $> n) ^ " is not a nat.");
               fail)
      end in
      info "iter" n.at ("Iter length n' = " ^ string_of_int n'');
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
        iterM (fun (x, e) ->
          let t = Il.Env.find_var !il_env x in
          let* e' = eval_exp !lctxr (IdxE (e, mk_nat idx) $$ e.at % t) in
          lctxr := VContext.add x.it e' !lctxr;
          return ()
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
      ) ctx' (0 -- n'') in
      il_env := il_env0;  (* Resume old environment *)
      return ctx''
    | ListN (_, None) | List | List1 -> assert false  (* Should have been compiled away by animation. *)
    | Opt ->
      let il_env0 = !il_env in
      (* Extend il_env with "local" variables in the iteration *)
      List.iter (fun (x, e) ->
        match e.it with
        | VarE x_question ->
          let t_question = Il.Env.find_var !il_env x_question in
          let t = Il_util.as_opt_typ !il_env t_question in
          il_env := Il.Env.(bind_var !il_env x t);
        | _ -> assert false
      ) (in_binds @ out_binds);
      info "iter" prem.at ("in-binds are: " ^ string_of_iterexp (iter, in_binds) ^ "\n" ^
                           "out-binds are: " ^ string_of_iterexp (iter, out_binds));
      (* Need to figure out whether it runs or not. *)
      let* in_vals = mapM (fun (x, e) -> let* e' = eval_exp ctx e in return (x, e')) in_binds in
      assert (List.length in_vals > 0);
      let run_opt = match (List.hd in_vals |> snd).it with
      | OptE None     -> false
      | OptE (Some _) -> true
      | _ -> assert false
      in
      (* Check that all inputs agree. *)
      List.iter (fun (_, opt_val) ->
        match opt_val.it, run_opt with
        | OptE None, false -> ()
        | OptE (Some _), true -> ()
        | _ -> assert false
      ) in_vals;
      let* ctx' = begin if not run_opt then
      (* When the optional is None, all outflow variables should be None. *)
        List.fold_left (fun ctx (x, e) ->
          match e.it with
          | VarE x_question -> VContext.add x_question.it (mk_none e.note) ctx
          | _ -> assert false
        ) ctx out_binds |> return
      else
      (* When the optional is Some *)
        let lctxr = ref ctx in
        (* In-flow *)
        List.iter (fun (x, opt_val) ->
          let OptE (Some val_) = opt_val.it in
          lctxr := VContext.add x.it val_ !lctxr
        ) in_vals;
        let* lctx = eval_prems !lctxr prems in
        lctxr := lctx;
        (* Out-flow *)
        List.iter (fun (x, e) ->
          match e.it with
          | VarE x_question ->
            let vx = VContext.find x.it !lctxr in
            let opt_vx_question = VContext.find_opt x_question.it !lctxr in
            begin match opt_vx_question with
            | Some vx_question -> assert false
            | None -> let some_vx = mk_some e.note vx in
                      lctxr := VContext.add x_question.it some_vx !lctxr
            end
          | _ -> assert false
        ) out_binds;
        return !lctxr
      end in
      il_env := il_env0;  (* Resume old environment *)
      return ctx'
    end
  | _ -> assert false

and eval_prems ctx prems : VContext.t OptMonad.m =
  match prems with
  | [] -> return ctx
  | prem :: prems ->
    let* ctx'  = eval_prem  ctx  prem  in
    let* ctx'' = eval_prems ctx' prems in
    return ctx''

and match_arg at (pat: arg) (arg: arg) : VContext.t option =
  match pat.it, arg.it with
  | TypA ptyp , TypA _    -> todo "match_arg TypA"
  | ExpA pexp , ExpA aexp -> (try Some (assign VContext.empty pexp aexp) with PatternMatchFailure -> fail)
  | DefA pid  , DefA _    -> todo "match_arg DefA"
  | GramA psym, GramA _   -> todo "match_arg GramA"
  | _ -> fail_log at ("Wrong argument sort: " ^ string_of_arg arg ^ " doesn't match pattern " ^ string_of_arg pat)


and match_args at pargs args : VContext.t option =
  match pargs, args with
  | [], [] -> return VContext.empty
  | parg::pargs', arg::args' ->
    let* vctx = match_arg at parg arg in
    let* vctx' = match_args at pargs' args' in
    return (VContext.union (fun k _ _ -> error at ("Duplicate variable `" ^ k ^ "`")) vctx vctx')

and match_clause at (fname: string) (clauses: clause list) (args: arg list) : exp OptMonad.m =
  info "match" at ("Match_clause: `" ^ fname ^ "`");
  match clauses with
  | [] -> fail_log at ("No function clause matches the input arguments in function `" ^ fname ^ "`")
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


and eval_func name func_def args : exp OptMonad.m =
  let (_, params, typ, fcs, _) = func_def.it in
  match_clause no_region name fcs args


and call_func name args : exp OptMonad.m =
  let* builtin_name, is_builtin =
    match Il.Env.find_func_hint !il_env name "builtin" with
    | None -> return (name, false)
    | Some hint ->
      match hint.hintexp.it with
      | SeqE []     -> return (name , true)  (* hint(builtin) *)
      | TextE fname -> return (fname, true)  (* hint(builtin "g") *)
      | _ -> fail_log no (sprintf "Ill-formed builtin hint for definition `%s`." name)
  in
  (* Function *)
  match Def.find_dl_func_def name !dl with
  | Some fdef when not is_builtin -> eval_func name fdef args
  (* Numerics *)
  | None when I.Numerics.mem builtin_name -> (
    if not is_builtin then
      warn no (sprintf "Numeric function `%s` is not defined in source, consider adding a hint(builtin)." name);
    (* Some (I.Numerics.call_numerics builtin_name args) *)
    error no "call_func: Can't call built-in functions for now; not yet implemented."
  )
  (* Relation *)
  | None when Relation.mem name -> Relation.call_func name args |> return
  | None -> fail_log no (sprintf "There is no function named `%s`." name)



(* Wasm interpreter entry *)

let instantiate (args: arg list) : exp =
  match call_func "instantiate" args with
  | Some e' -> e'
  | None    -> raise (Failure "Interpreter failed at $instantiate.")

let invoke (args: arg list) : exp =
  match call_func "invoke" args with
  | Some e' -> e'
  | None    -> raise (Failure "Interpreter failed at $invoke.")
