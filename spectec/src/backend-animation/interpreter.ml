open Il_util
open Construct
open Def
open State
open Util
open Lib.Time
open Lib.Fun
open Error
open Il.Ast
open Il.Print
open Source
open Printf
open Il2al.Free
module A = Al.Ast
module I = Backend_interpreter
module RI = Reference_interpreter



(* Errors *)

let verbose : string list ref =
  ref [
      (* "table"; *)
      (* "assertion"; *)
      (* "eval"; *)          (* Evaluation of expressions. *)
      (* "assign"; *)        (* Matching, but for terms only. *)
      (* "match";  *)        (* Matching of other types. *)
      (* "match_info";  *)
      (* "steps";       *)
      (* "call"; *)
      (* "iter"; *)          (* Low-level debugging. *)
      ]


let error at msg = Error.error at "animation/interpreter" msg
let error_np msg = error no_region msg

let error_value name exp = error exp.at ("Invalid " ^ name ^ ": " ^ string_of_exp exp)
let error_values name exps =
  let at = over_region (List.map (fun e -> e.at) exps) in
  error at ("Invalid " ^ name ^ ": " ^ String.concat ", " (List.map string_of_exp exps))

let string_of_error at msg = string_of_region at ^ " (Meta)Interpreter error:\n" ^ msg

let warn at msg = print_endline (string_of_region at ^ " (Meta)Interpreter warning:\n" ^ msg)

let info v at msg = if List.mem v !verbose || v = "" then
                      print_endline (string_of_region at ^ " (Meta)Interpreter info[" ^ v ^ "]:\n" ^ msg)
                    else
                      ()

let assert_msg cond msg = if not cond then info "assertion" no msg; assert cond


(* Helper *)


let (--) start end_ : int list = List.init (end_ - start) (fun i -> start + i)

module OptMonad : sig
  include Lib.Monad
  val opt_lift : 'a option -> 'a m
  val run_opt : 'a m -> 'a option
end = struct
  type 'a m = 'a option
  let return a = Some a
  let fail ()  = None
  let ( <$> ) = Option.map
  let ( <&> ) ma f = f <$> ma
  let ( >>= ) = Option.bind
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let rec mapM f = function
    | [] -> return []
    | x::xs -> let* x'  = f x in
               let* xs' = mapM f xs in
               return (x'::xs')
  let opt_mapM f = function
    | None -> return None
    | Some a -> let* b = f a in return (Some b)
  let mapiM f xs =
    let rec mapiM' f i = function
    | [] -> return []
    | x::xs -> let* x'  = f i x in
               let* xs' = mapiM' f (i+1) xs in
               return (x'::xs')
    in
    mapiM' f 0 xs
  let iterM f xs = mapM f xs >> return ()
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs

  let opt_lift : 'a option -> 'a m = Fun.id
  let run_opt : 'a m -> 'a option = Fun.id
end

open OptMonad


type builtin = { name : string; f : exp list -> exp OptMonad.m }
type il_builtin = { name : string; f : exp list -> exp }

let get_builtin_name : builtin -> string = fun b -> b.name
let get_il_builtin_name : il_builtin -> string = fun b -> b.name


let fail_info cat at msg = info cat at msg; fail ()

let error_eval etyp exp onotes =
  let notes = match onotes with
  | None     -> ""
  | Some msg -> "\n  ▹ " ^ msg
  in
  error exp.at (etyp ^ " can't evaluate: " ^ string_of_exp exp ^ notes)

let fail_assign at lhs rhs msg =
  info "assign" at ("Pattern-matching failed (" ^ msg ^ "):\n" ^
                   "  ▹ pattern: " ^ string_of_exp lhs ^ "\n" ^
                   "  ▹ value: " ^ string_of_exp rhs);
  fail ()

let string_of_exp exp = Il.Print.string_of_exp exp |> Lib.String.shorten
let string_of_arg arg = Il.Print.string_of_arg arg |> Lib.String.shorten
let string_of_args = function
  | [] -> ""
  | as_ -> "(" ^ concat ", " (List.map string_of_arg as_) ^ ")"

(* Environments *)

module VContext = struct
  include Il.Subst
  type t = subst

  let find_opt_varid : subst -> id -> exp option = fun ctx n -> Map.find_opt n.it ctx.varid
  let dom_varid ctx : Set.t = ctx.varid |> Map.bindings |> List.map fst |> Set.of_list
end


let dl : dl_def list ref = ref []
let il_env : Il.Env.t ref = ref Il.Env.empty


(** [lhs] is the pattern, and [rhs] is the expression. *)
let rec assign ctx (lhs: exp) (rhs: exp) : VContext.t OptMonad.m =
  let* rhs' = eval_exp ctx rhs in
  match lhs.it, rhs'.it with
  | VarE name, _ ->
    VContext.add_varid ctx name rhs' |> return
  | IterE ({ it = VarE x1; _ }, ((List|List1), [(x2, lhs')])), ListE _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs'
  | IterE ({ it = VarE x1; _ }, (Opt, [x2, lhs'])), _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs'
  | IterE (e, (Opt, xes)), _ ->
    assert false  (* Animation shouldn't output this. *)
  | IterE (e, ((ListN _|List|List1) as iter, xes)), ListE es ->
    let* ctxs = mapM (assign VContext.empty e) es in
    (* Assign length variable *)
    let* ctx' =
      match iter with
      | ListN (expr, None) ->
        let length = il_of_nat (List.length es) in
        assign ctx expr length
      | ListN _ -> fail ()
      | _ -> return ctx
    in
    foldlM (fun ctx (x, e) ->
      let vs = List.map (Fun.flip VContext.find_varid x) ctxs in
      let v = match iter with
      | Opt -> optE e.note (List.nth_opt vs 0)
      | _   -> listE e.note vs
      in
      assign ctx e v
    ) ctx' xes
  | TupE lhs_s, TupE rhs_s when List.length lhs_s = List.length rhs_s ->
    foldlM (fun c (p, e) -> assign c p e) ctx (List.combine lhs_s rhs_s)
  | CaseE (lhs_tag, lhs_s), CaseE (rhs_tag, rhs_s) ->
    begin match lhs_s.it, rhs_s.it with
    | TupE lhs_s', TupE rhs_s' ->
      if Il.Eq.eq_mixop lhs_tag rhs_tag && List.length lhs_s' = List.length rhs_s' then
        foldlM (fun c (p, e) -> assign c p e) ctx (List.combine lhs_s' rhs_s')
      else
        fail ()
    | _ -> fail ()
    end
  | OptE (Some lhs'), OptE (Some rhs'') -> assign ctx lhs' rhs''
  | CvtE (e1, nt, _), NumE n ->
    (match Xl.Num.cvt nt n with
    | Some n' -> assign ctx e1 (mk_expr rhs'.at (NumT nt $ rhs'.at) (NumE n'))
    | None -> fail ()
    )
  | SubE (p, pt1, pt2), SubE (e, et1, et2) when Il.Eq.eq_typ pt1 et1 && Il.Eq.eq_typ pt2 et2 -> assign ctx p e
  | SubE (p, t1, t2), _ when Il.Eq.eq_typ t1 rhs'.note -> assign ctx p rhs'
  | SubE (p, t1, t2), CaseE (mixop, tup) when Il.Eq.eq_typ t2 rhs'.note ->
    let tcs = as_variant_typ !il_env t1 in
    (match List.find_map (fun (mixop', _, _) -> if Il.Eq.eq_mixop mixop mixop' then Some mixop' else None) tcs with
    | Some mixop' ->
      let rhs'' = CaseE (mixop', tup) $$ rhs'.at % t1 in
      assign ctx p rhs''
    | None -> fail ()
    )
  (*
    if sub_typ env e1.note t21 then
      match_exp' env s (reduce_exp env (SubE (e1, e1.note, t21) $> e21)) e21
    else if is_head_normal_exp e1 then
      let t21' = reduce_typ env t21 in
      if
        match e1.it, t21'.it with
        | BoolE _, BoolT
        | NumE _, NumT _
        | TextE _, TextT -> true
        | CaseE (op, _), VarT _ ->
          (match (reduce_typdef env t21).it with
          | VariantT tcs ->
            (* Assumes that we only have shallow subtyping. *)
            List.exists (fun (opN, _, _) -> Eq.eq_mixop opN op) tcs
          | _ -> false
          )
        | VarE id1, _ ->
          let t1 = reduce_typ env (Env.find_var env id1) in
          sub_typ env t1 t21 || raise Irred
        | _, _ -> false
      then match_exp' env s {e1 with note = t21} e21
      else None
    else raise Irred
  *)
  | _, _ -> fail ()


and is_value : exp -> bool = Il.Eval.is_normal_exp
and is_hnf   : exp -> bool = Il.Eval.is_head_normal_exp

and eval_exp ?full:(full=true) ctx exp : exp OptMonad.m =
  let open Xl in
  match exp.it with
  | _ when is_value exp -> return exp
  | _ when is_hnf exp && not full -> return exp
  | VarE v -> (match VContext.find_opt_varid ctx v with
              | Some v' -> return v'
              | None -> error exp.at (sprintf "Variable `%s` is not in the value context.\n  ▹ vctx: %s" v.it
                                       (string_of_varset (VContext.dom_varid ctx)))
              )
  | BoolE _ | NumE _ | TextE _ -> return exp
  | UnE (op, _, e1) ->
    let* e1' = eval_exp ctx e1 in
    (match op, e1'.it with
    | #Bool.unop as op', BoolE b1 -> BoolE (Bool.un op' b1) $> exp |> return
    | #Num.unop  as op', NumE  n1 ->
      (match Num.un op' n1 with
      | Some v -> NumE v $> exp |> return
      | None -> error_eval "Numeric unary expression" exp None
      )
    | _ -> error_eval "Unary expression" exp None
    )
  | BinE (op, ot, e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match op with
    | #Bool.binop as op' ->
      (match Bool.bin_partial op' e1'.it e2'.it of_bool_exp to_bool_exp with
      | Some v -> v $> exp |> return
      | None -> error_eval "Boolean binary expression" exp None
      )
    | #Xl.Num.binop as op' ->
      (match Num.bin_partial op' e1'.it e2'.it of_num_exp to_num_exp with
      | Some v -> v $> exp |> return
      | None -> error_eval "Numeric binary expression" exp None
      )
    )
  | CmpE (op, ot, e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match op, e1'.it, e2'.it with
    | `EqOp, _, _ when Il.Eq.eq_exp e1' e2' -> BoolE true
    | `NeOp, _, _ when Il.Eq.eq_exp e1' e2' -> BoolE false
    | `EqOp, _, _ when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE false
    | `NeOp, _, _ when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE true
    | #Num.cmpop as op', NumE n1, NumE n2 ->
      (match Num.cmp op' n1 n2 with
      | Some b -> BoolE b
      | None -> error_eval "Numeric comparison expresion" exp None
      )
    | _ -> error_eval "Comparison expression" exp None
    ) $> exp |> return
  | IdxE (e1, e2) ->
    let* e1' = eval_exp ~full:false ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es, NumE (`Nat i) ->
      if i < Z.of_int (List.length es) then
        List.nth es (Z.to_int i) |> eval_exp ~full ctx
      else
        error_eval "Indexing expression" exp
          (Some ("Index out-of-range:\n" ^
                 "seq   = " ^ string_of_exp e1' ^ "\n" ^
                 "|seq| = " ^ string_of_int (List.length es) ^ "\n" ^
                 "idx   = " ^ string_of_int (Z.to_int i)
                )
          )
    | _ -> error_eval "Indexing expression" exp
             (Some ("seq = " ^ string_of_exp e1' ^ "; idx = " ^ string_of_exp e2'))
    )
  | SliceE (e1, e2, e3) ->
    let* e1' = eval_exp ~full ctx e1 in
    let* e2' = eval_exp ctx e2 in
    let* e3' = eval_exp ctx e3 in
    (match e1'.it, e2'.it, e3'.it with
    | ListE es, NumE (`Nat i), NumE (`Nat n) ->
      if Z.(i + n) <= Z.of_int (List.length es) then
        ListE (Lib.List.take (Z.to_int n) (Lib.List.drop (Z.to_int i) es)) $> exp |> return
      else
        error_eval "Slicing expression" exp
          (Some ("|es| = " ^ string_of_int (List.length es) ^
                 "; i = " ^ string_of_int (Z.to_int i) ^
                 "; n = " ^ string_of_int (Z.to_int n)))
    | _ -> error_eval "Slicing expression" exp
             (Some (string_of_exp e1' ^ "[" ^ string_of_exp e2' ^ ":" ^ string_of_exp e3' ^ "]"))
    )
  | UpdE (e1, p, e2) ->
    let* e1' = eval_exp ~full ctx e1 in
    let* e2' = eval_exp ~full ctx e2 in
    eval_path ctx e1' p
      (fun e' p' ->
        if p'.it = RootP
        then return e2'
        else error_eval "Sequence update expression" exp None
      )
  | ExtE (e1, p, e2) ->
    let* e1' = eval_exp ~full ctx e1 in
    let* e2' = eval_exp ~full ctx e2 in
    eval_path ctx e1' p
      (fun e' p' ->
        if p'.it = RootP
        then eval_exp ~full ctx (CatE (e', e2') $> e')
        else error_eval "Sequence extension expression" exp None
      )
  | StrE efs -> let* efs' = mapM (eval_expfield ctx) efs in StrE efs' $> exp |> return
  | DotE (e1, atom) ->
    let* e1' = eval_exp ~full:false ctx e1 in
    (match e1'.it with
    | StrE efs -> snd (List.find (fun (atomN, _) -> Atom.eq atomN atom) efs) |> return
    | _ -> error_eval "Struct dot expression" exp None
    )
  | CompE (e1, e2) ->
    (* TODO(4, rossberg): avoid overlap with CatE? *)
    let* e1' = eval_exp ~full ctx e1 in
    let* e2' = eval_exp ~full ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es1, ListE es2 -> ListE (es1 @ es2) |> return
    | OptE None, OptE _ -> e2'.it |> return
    | OptE _, OptE None -> e1'.it |> return
    | StrE efs1, StrE efs2 ->
      let merge (atom1, e1) (atom2, e2) =
        assert (Atom.eq atom1 atom2);
        let* e12' = eval_exp ~full ctx (CompE (e1, e2) $> e1) in
        return (atom1, e12')
      in
      let* efs12' = mapM (Lib.Fun.uncurry merge) (List.combine efs1 efs2) in
      StrE efs12' |> return
    | _ -> error_eval "Sequence composition expression" exp None
    ) <&> (fun e' -> e' $> exp)
  | MemE (e1, e2) ->
    let* e1' = eval_exp ctx e1 in
    let* e2' = eval_exp ctx e2 in
    (match e2'.it with
    | OptE None -> BoolE false
    | OptE (Some e2') when Il.Eq.eq_exp e1' e2' -> BoolE true
    | OptE (Some e2') when Il.Eval.is_normal_exp e1' && Il.Eval.is_normal_exp e2' -> BoolE false
    | ListE [] -> BoolE false
    | ListE es2' when List.exists (Il.Eq.eq_exp e1') es2' -> BoolE true
    | ListE _ -> BoolE false
    | _ -> error_eval "Membership expression" exp None
    ) $> exp |> return
  | LenE e1 ->
    let* e1' = eval_exp ~full:false ctx e1 in
    (match e1'.it with
    | ListE es -> NumE (`Nat (Z.of_int (List.length es))) $> exp |> return
    | _ -> error_eval "Sequence length expression" exp None
    )
  | TupE es -> let* es' = mapM (eval_exp ~full ctx) es in TupE es' $> exp |> return
  | CallE (fid, args) ->
    let* args' = mapM (eval_arg ctx) args in
    call_func fid.it args'
  | IterE (e1, iterexp) ->
    let* (iter', xes') as iterexp' = eval_iterexp ctx iterexp in
    let ids, es' = List.split xes' in
    if iter' <= List1 && es' = [] then
      error_eval "Iterated expression" exp (Some "Inadequate information about the iteration scheme.")
    else
      (match iter' with
      | Opt ->
        let eos' = List.map unwrap_opt es' in
        if List.for_all Option.is_none eos' then
          OptE None $> exp |> return
        else if List.for_all Option.is_some eos' then
          let es1' = List.map Option.get eos' in
          let* ctx' = foldlM (fun c (a, b) ->
            let* b' = eval_exp c b in
            VContext.add_varid c a b' |> return
          ) ctx (List.combine ids es1') in
          let* e1' = eval_exp ~full ctx' e1 in
          OptE (Some e1') $> exp |> return
        else
          error_eval "Iterated epxression" exp (Some "?-iterator inflow expressions don't match.")
      | List | List1 ->
        let n = List.length (elts_of_list (List.hd es')) in
        if iter' = List || n >= 1 then
          let en = NumE (`Nat (Z.of_int n)) $$ exp.at % (NumT `NatT $ exp.at) in
          eval_exp ~full ctx (IterE (e1, (ListN (en, None), xes')) $> exp)
        else
          error_eval "Iterated expression" exp (Some "Using +-iterator but sequence length is 0")
      | ListN ({it = NumE (`Nat n'); _}, ido) ->
        let ess' = List.map elts_of_list es' in
        let ns = List.map List.length ess' in
        let n = Z.to_int n' in
        if List.for_all ((=) n) ns then
          let* e1s' = mapM (fun i ->
            let esI' = List.map (fun es -> List.nth es i) ess' in
            let ctx' = List.fold_left2 VContext.add_varid ctx ids esI' in
            let ctx'' =
              Option.fold ido ~none:ctx' ~some:(fun id ->
                let en = NumE (`Nat (Z.of_int i)) $$ id.at % (NumT `NatT $ id.at) in
                VContext.add_varid ctx' id en
              )
            in eval_exp ~full ctx'' e1
          ) (0 -- n)
          in
          ListE e1s' $> exp |> return
        else
          error_eval "Iterated expression" exp (Some "Inflow sequences don't agree on the length")
      | ListN _ -> error_eval "Iterated expression" exp None
      )
  | ProjE (e1, i) ->
    let* e1' = eval_exp ~full ctx e1 in
    (match e1'.it with
    | TupE es -> List.nth es i |> return
    | _ -> error_eval "Tuple projection expression" exp None
    )
  | UncaseE (e1, mixop) ->
    let* e1' = eval_exp ~full ctx e1 in
    (match e1'.it with
    | CaseE (mixop', e11') when Il.Eq.eq_mixop mixop mixop' -> return e11'
    | _ -> error_eval "Constructor unwrapping expression" exp
                     (Some ("e1 ⤳ " ^ string_of_exp e1' ^ "; mixop = " ^ string_of_mixop mixop))
    )
  | OptE oe1 -> let* oe1' = opt_mapM (eval_exp ctx) oe1 in OptE oe1' $> exp |> return
  | TheE e1 ->
    let* e1' = eval_exp ~full ctx e1 in
    (match e1'.it with
    | OptE (Some e11) -> return e11
    | _ -> error_eval "THE expression" exp None
    )
  | ListE es -> let* es' = mapM (eval_exp ~full ctx) es in ListE es' $> exp |> return
  | LiftE e1 ->
    let* e1' = eval_exp ~full ctx e1 in
    (match e1'.it with
    | OptE None -> ListE []
    | OptE (Some e11') -> ListE [e11']
    | _ -> error_eval "Option lifting expression" exp None
    ) $> exp |> return
  | CatE (e1, e2) ->
    let* e1' = eval_exp ~full ctx e1 in
    let* e2' = eval_exp ~full ctx e2 in
    (match e1'.it, e2'.it with
    | ListE es1, ListE es2 -> ListE (es1 @ es2)
    | OptE None, OptE _ -> e2'.it
    | OptE _, OptE None -> e1'.it
    | _ -> error_eval "Sequence concatenation expression" exp None
    ) $> exp |> return
  | CaseE (op, e1) -> let* e1' = eval_exp ~full ctx e1 in CaseE (op, e1') $> exp |> return
  | CvtE (e1, _nt1, nt2) ->
    let* e1' = eval_exp ctx e1 in
    (match e1'.it with
    | NumE n ->
      (match Num.cvt nt2 n with
      | Some n' -> NumE n' $> exp |> return
      | None -> error_eval "Numeric type conversion" exp (Some "Cannot perform conversion.")
      )
    | _ -> error_eval "Numeric type conversion" exp (Some ("Not a numeric:" ^ string_of_exp e1))
    )
  | SubE (e1, t1, t2) when Il.Eval.equiv_typ !il_env t1 t2 -> eval_exp ctx e1
  (* Pushes down the SubE node into the leaves of the value. *)
  | SubE (e1, t1, t2) ->
    let* e1' = eval_exp ~full ctx e1 in
    let t1' = Il.Eval.reduce_typ !il_env t1 in
    let t2' = Il.Eval.reduce_typ !il_env t2 in
    (match e1'.it with
    | SubE (e11', t11', _t12') -> eval_exp ~full ctx (SubE (e11', t11', t2') $> exp)  (* FIXME(zilinc): I don't think this can ever happen. *)
    | CaseE (mixop, tup) ->
      let tcs = as_variant_typ !il_env t2' in
      (match List.find_map (fun (mixop', _, _) -> if Il.Eq.eq_mixop mixop mixop' then Some mixop' else None) tcs with
      | Some mixop' -> CaseE (mixop', tup) $$ e1'.at % t2' |> return
      | None -> error_eval "Subtyping expression" exp
                           (Some ("Mixop " ^ string_of_mixop mixop ^ " not in the supertype " ^ string_of_typ t2'))
      )
    | TupE es' ->
      (* FIXME(zilinc): Do it properly. *)
      (match t1.it, t2.it with
      | TupT ets1, TupT ets2 ->
        let* (_, _, res') =
          foldlM (fun opt (eI, ((e1I, t1I), (e2I, t2I))) ->
            let (s1, s2, res') = opt in
            let t1I' = Il.Subst.subst_typ s1 t1I in
            let t2I' = Il.Subst.subst_typ s2 t2I in
            let* e1I' = eval_exp ctx (Il.Subst.subst_exp s1 e1I) in
            let* e2I' = eval_exp ctx (Il.Subst.subst_exp s2 e2I) in
            let* s1' = try Il.Eval.match_exp !il_env s1 eI e1I' |> opt_lift with Il.Eval.Irred -> fail () in
            let* s2' = try Il.Eval.match_exp !il_env s2 eI e2I' |> opt_lift with Il.Eval.Irred -> fail () in
            let* eI' = eval_exp ~full ctx (SubE (eI, t1I', t2I') $$ eI.at % t2I') in
            return (s1', s2', eI'::res')
          ) (Il.Subst.empty, Il.Subst.empty, []) (List.combine es' (List.combine ets1 ets2))
        in
        TupE (List.rev res') $> exp |> return
      | _ -> error_eval "Subtyping expression" exp (Some "Invalid type for tuple expression.")
      )
    | _ -> SubE (e1', t1, t2) $> exp |> return
    )
  (* | _ -> todo "eval_exp: unmatched cases" *)

and eval_iter ctx = function
  | ListN (e, ido) -> let* e' = eval_exp ctx e in ListN (e', ido) |> return
  | iter -> return iter

and eval_iterexp ctx (iter, xes) : iterexp OptMonad.m =
  let* iter' = eval_iter ctx iter in
  let excl_ids = match iter with
  | ListN(_, Some i) -> [i.it]
  | _ -> []
  in
  (* Remove the outflowing binding. *)
  let xes' = List.filter (fun (x, e) -> List.mem x.it excl_ids |> not) xes in
  let* xes'' = mapM (fun (id, e) -> let* e' = eval_exp ctx e in return (id, e')) xes' in
  return (iter', xes'')

and eval_expfield ?full:(full=true) ctx (atom, e) : expfield OptMonad.m =
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
      | _ -> error e.at ("Index path failed to evaluate:\n" ^
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
      | _ -> error e.at ("Slice path failed to evaluate:\n" ^
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
      | _ -> error e.at ("Dot path failed to evaluate:\n" ^
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
  match prem.it with
  | ElsePr -> return ctx
  | LetPr (lhs, rhs, _vs) -> assign ctx lhs rhs
  | IfPr e ->
    let* b = eval_exp ctx e in
    if b.it = BoolE true then return ctx
    else
      fail ()
  | IterPr (prems, (iter, xes)) ->
    (* Work out which variables are inflow and which are outflow. *)
    let in_binds, out_binds = List.fold_right (fun (x, e) (ins, ous) ->
      let fv_e = (free_exp false e).varid in
      if Set.subset fv_e (VContext.dom_varid ctx) then
        (x, e)::ins, ous
      else
        ins, (x, e)::ous
    ) xes ([], []) in
    begin match iter with
    | ListN (n, Some i) ->
      let* n' = eval_exp ctx n in
      let* n'' = begin match n'.it with
      | NumE (`Nat n'') -> return (Z.to_int n'')
      | n'' -> fail ()
      end in
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
      (* Initialise the out-vars, so that even when n' = 0 they are still assigned to `eps`. *)
      let ctx' = List.fold_left (fun ctx (x, e) ->
        match e.it with
        | VarE x_star ->
          let vx_star = ListE [] $$ no_region % e.note in
          VContext.add_varid ctx x_star vx_star
        | _ -> assert false
      ) ctx out_binds in
      (* Run the loop *)
      let* ctx'' = foldlM (fun ctx idx ->
        let lctxr = ref ctx in
        lctxr := VContext.add_varid !lctxr i (mk_nat idx);
        (* In-flow *)
        let* () = iterM (fun (x, e) ->
          let t = Il.Env.find_var !il_env x in
          let* e' = eval_exp !lctxr (IdxE (e, mk_nat idx) $$ e.at % t) in
          lctxr := VContext.add_varid !lctxr x e';
          return ()
        ) in_binds
        in
        let* lctx = eval_prems !lctxr prems in
        lctxr := lctx;
        (* Out-flow *)
        List.iter (fun (x, e) ->
          match e.it with
          | VarE x_star ->
            let vx = VContext.find_varid !lctxr x in
            let opt_vx_star = VContext.find_opt_varid !lctxr x_star in
            begin match opt_vx_star with
            | Some vx_star ->
              begin match vx_star.it with
              | ListE es -> let vx_star' = ListE (es @ [vx]) $> vx_star in
                            lctxr := VContext.add_varid !lctxr x_star vx_star'
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
          | VarE x_question -> VContext.add_varid ctx x_question (mk_none e.note)
          | _ -> assert false
        ) ctx out_binds |> return
      else
      (* When the optional is Some *)
        let lctxr = ref ctx in
        (* In-flow *)
        List.iter (fun (x, opt_val) ->
          let OptE (Some val_) = opt_val.it in
          lctxr := VContext.add_varid !lctxr x val_
        ) in_vals;
        let* lctx = eval_prems !lctxr prems in
        lctxr := lctx;
        (* Out-flow *)
        List.iter (fun (x, e) ->
          match e.it with
          | VarE x_question ->
            let vx = VContext.find_varid !lctxr x in
            let opt_vx_question = VContext.find_opt_varid !lctxr x_question in
            begin match opt_vx_question with
            | Some vx_question -> assert false
            | None -> let some_vx = mk_some e.note vx in
                      lctxr := VContext.add_varid !lctxr x_question some_vx
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

and match_typ ctx at (pat: typ) (arg: typ) : VContext.t OptMonad.m =
  match pat.it, arg.it with
  | VarT (pid, []), _ ->
    let arg' = Il.Eval.reduce_typ !il_env arg in
    VContext.add_typid ctx pid arg' |> return
  | _ -> fail ()


and match_arg ctx at (pat: arg) (arg: arg) : VContext.t OptMonad.m =
  match pat.it, arg.it with
  | TypA ptyp , TypA atyp -> match_typ ctx at ptyp atyp
  | ExpA pexp , ExpA aexp -> assign ctx pexp aexp
  | DefA pid  , DefA _    -> todo "match_arg DefA"
  | GramA psym, GramA _   -> todo "match_arg GramA"
  | _ -> fail ()


and match_args ctx at pargs args : VContext.t OptMonad.m =
  match pargs, args with
  | [], [] -> return ctx
  | parg::pargs', arg::args' ->
    let* ctx'  = match_arg  ctx  at parg   arg   in
    let* ctx'' = match_args ctx' at pargs' args' in
    return ctx''

and match_clause at (fname: string) (nth: int) (clauses: clause list) (args: arg list) : exp OptMonad.m =
  match clauses with
  | [] -> fail ()
  | cl :: cls ->
    let DefD (binds, pargs, exp, prems) = cl.it in
    let old_env = ref !il_env in
    (* Add bindings to [il_env]. *)
    let _ = Animate.env_of_binds binds il_env in
    assert (List.length pargs = List.length args);
    let* val_ =
      (match match_args VContext.empty cl.at pargs args |> run_opt with
      | Some ctx ->
        begin match eval_prems ctx prems |> run_opt with
        | Some ctx' -> eval_exp ctx' exp
        | None      -> match_clause at fname (nth+1) cls args
        end
      | None -> match_clause at fname (nth+1) cls args
      )
    in
    (* Resume global environment. *)
    il_env := !old_env;
    return val_


and eval_func name func_def args : exp OptMonad.m =
  let (_, params, typ, fcs, _) = func_def.it in
  match_clause no_region name 1 fcs args


and call_func name args : exp OptMonad.m =
  match name with
  (* Hardcoded functions defined in meta.spectec *)
  | "Steps"  -> call_func "steps"    args
  | "Step"   -> call_func "step"     args
  (* Hardcoded functions defined in the compiler. *)
  | "Module_ok"     -> module_ok     args |> return
  | "Externaddr_ok" -> externaddr_ok args |> return
  | "Ref_ok"        -> ref_ok        args |> return
  | "Val_ok"        -> val_ok        args |> return
  (* Others *)
  | _ ->
    let builtin_name, is_builtin =
      match Il.Env.find_func_hint !il_env name "builtin" with
      | None -> (name, false)
      | Some hint ->
        match hint.hintexp.it with
        | SeqE []     -> (name , true)  (* hint(builtin) *)
        | TextE fname -> (fname, true)  (* hint(builtin "g") *)
        | _ -> error no (sprintf "Ill-formed builtin hint for definition `%s`." name)
    in
    (match Def.find_dl_func_def name !dl with
    (* Regular function definition. *)
    | Some fdef when not is_builtin -> eval_func name fdef args
    (* Builtins and numerics *)
    | Some { it = (_, _, _, [], _); at; _ } when is_builtin ->
      if Numerics.mem builtin_name then
        Numerics.call_numerics builtin_name args |> return
      else if builtins_mem builtin_name then
        call_builtins builtin_name args
      else
        error no (sprintf "Builtin function `%s` is not defined in the interpreter." name)
    | _ when is_builtin ->
      error no (sprintf "Function `%s` is marked as builtin but there is either no declaration or is defined in SpecTec." name)
    | None -> error no (sprintf "There is no function named `%s`." name)
    )


(* Host instructions *)

and is_host = function
  | "print" | "print_i32" | "print_i64" | "print_f32" | "print_f64" | "print_i32_f32" | "print_f64_f64" -> true
  | _ -> false

and call_hostfunc name s vs =
  (* ty ∈ {"I32", "I64", "F32", "F64"} *)
  let as_const ty e = match e.it with
  | CaseE (tag, { it = TupE [nt; n]; _ })
  | OptE (Some {it = CaseE (tag, { it = TupE [nt; n]; _ }); _})
  -> if mixop_to_text tag = [["CONST"];[];[]] then
      (match match_caseE "numtype" nt with
      | [[ty']], [] when ty = ty' -> n
      | _ -> error_value "numtype" nt
      )
     else
      error_value "const" e
  | _ -> error no ("Host function call: Not " ^ ty ^ ".CONST: " ^ string_of_exp e)
  in
  let argc = List.length vs in
  (match name with
  | "print" when argc = 0 -> print_endline "- print: ()"
  | "print_i32" when argc = 1 ->
    List.hd vs
    |> as_const "I32"
    |> il_to_uN_32
    |> RI.I32.to_string_s
    |> Printf.printf "- print_i32: %s\n"
  | "print_i64" when argc = 1 ->
    List.hd vs
    |> as_const "I64"
    |> il_to_uN_64
    |> RI.I64.to_string_s
    |> Printf.printf "- print_i64: %s\n"
  | "print_f32" when argc = 1 ->
    List.hd vs
    |> as_const "F32"
    |> il_to_float32
    |> RI.F32.to_string
    |> Printf.printf "- print_f32: %s\n"
  | "print_f64" when argc = 1 ->
    List.hd vs
    |> as_const "F64"
    |> il_to_float64
    |> RI.F64.to_string
    |> Printf.printf "- print_f64: %s\n"
  | "print_i32_f32" when argc = 2 ->
    let [v1; v2] = vs in
    let i32 = v1 |> as_const "I32" |> il_to_nat32   |> RI.I32.to_string_s in
    let f32 = v2 |> as_const "F32" |> il_to_float32 |> RI.F32.to_string   in
    Printf.printf "- print_i32_f32: %s %s\n" i32 f32
  | "print_f64_f64" when argc = 2 ->
    let [v1; v2] = vs in
    let f64  = v1 |> as_const "F64" |> il_to_float64 |> RI.F64.to_string in
    let f64' = v2 |> as_const "F64" |> il_to_float64 |> RI.F64.to_string in
    Printf.printf "- print_f64_f64: %s %s\n" f64 f64'
  | name -> error no ("Invalid host function call: " ^ name)
  );
  (s, mk_case (t_var "result") [["_VALS"];[]] [listE (t_star "val") []])


and hostcall : builtin = {
  name = "hostcall";
  f =
    function
    | [hostfunc; s; args] ->
      (match match_caseE "hostfunc" hostfunc with
      | [["_HOSTFUNC"]; []], [{it = TextE fname; _}] ->
        let vs = elts_of_list args in
        let s', result = call_hostfunc fname s vs in
        mk_singleton (mk_case (t_var "hostcallresult") [["RES"];[];[]] [s'; result]) |> return
      | _ -> error_value ("Not a hostfunc") hostfunc
      )
    | vs -> error_values ("Args to $hostcall") vs
}


(* Built-in functions (meta.spectec) *)


and use_step : builtin= {
  name = "use_step";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step") |> return
      | None -> boolE false |> return
      )
    | es -> error_values ("Args to $use_step") es
}
and use_step_pure : builtin = {
  name = "use_step_pure";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step_pure") |> return
      | None -> boolE false |> return
      )
    | es -> error_values ("Args to $use_step_pure") es
}
and use_step_read : builtin = {
  name = "use_step_read";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step_read") |> return
      | None -> boolE false |> return
      )
    | es -> error_values ("Args to $use_step_read") es
}
and use_step_ctxt : builtin = {
  name = "use_step_ctxt";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      List.mem (List.hd (List.hd mixop)) ["LABEL_"; "FRAME_"; "HANDLER_"] |> boolE |> return
    | es -> error_values ("Args to $use_step_ctxt") es
}


and dispatch_step : builtin = {
  name = "dispatch_step";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step" -> call_func (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step") es
}
and dispatch_step_pure : builtin = {
  name = "dispatch_step_pure";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_pure" -> call_func (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step_pure rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step_pure") es
}
and dispatch_step_read : builtin = {
  name = "dispatch_step_read";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_read" -> call_func (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step_read rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step_read") es
}

and step_read_throw_ref_handler : builtin = {
  name = "Step_read_throw_ref_handler";
  f =
    function
    | [arg] -> call_func "Step_read/throw_ref" [expA arg]
}

and builtin_list : builtin list = [
  use_step; use_step_pure; use_step_read; use_step_ctxt;
  dispatch_step; dispatch_step_pure; dispatch_step_read;
  step_read_throw_ref_handler; hostcall;
  ]

and call_builtins fname args : exp OptMonad.m =
  match List.find_opt (fun numerics -> get_builtin_name numerics = fname) builtin_list with
  | Some builtin ->
    let args' = List.map (fun a -> match a.it with
    | ExpA e -> e
    | _ -> raise (Failure ("Wrong argument to builtin function " ^ fname ^ ": " ^ string_of_arg a))
    ) args in
    builtin.f args'
  | None -> raise (Failure ("Unknown builtin: " ^ fname))


and builtins_mem fname =
  List.exists (fun builtin -> get_builtin_name builtin = fname) builtin_list


(* Hard-coded relations *)


(* $Module_ok : module -> moduletype *)
and module_ok args : exp =
  match args with
  | [ {it = ExpA module_; _} ] ->
    let module_' = il_to_module module_ in
    let ModuleT (its, ets) = RI.Valid.check_module module_' in
    let importtypes = List.map (fun (RI.Types.ImportT (_, _, xt)) -> il_of_externtype xt) its in
    let exporttypes = List.map (fun (RI.Types.ExportT (_,    xt)) -> il_of_externtype xt) ets in
    mk_case' "moduletype" [[];["->"];[]] [ listE (t_star "externtype") importtypes; listE (t_star "externtype") exporttypes ]
  | _ -> error no ("Wrong number/type of arguments to $Module_ok.")

(* $Externaddr_ok : store -> externaddr -> externtype -> bool *)
and externaddr_ok args =
  match List.map it args with
  | [ ExpA s; ExpA eaddr; ExpA etype ] ->
    (match match_caseE "externaddr" eaddr with
    | [[name];[]], [{it = NumE (`Nat z); _}] ->
      let addr = Z.to_int z in
      let externaddr_type =
        name^"S"
        |> Store.access
        |> elts_of_list
        |> Fun.flip List.nth addr
        |> find_str_field "TYPE"
        |> fun type_ -> mk_case' "externtype" [[name];[]] [type_]
        |> Construct.il_to_externtype
      in
      let externtype = Construct.il_to_externtype etype in
      boolE (RI.Match.match_externtype [] externaddr_type externtype)
    | _ -> error_value "$Externaddr_ok (externaddr)" eaddr
    )
  | _ -> error no ("Wrong number/type of arguments to $Externaddr_ok.")

(* $Val_ok : store -> val -> valtype -> bool *)
and val_ok args =
  match List.map it args with
  | [ ExpA s; ExpA val_; ExpA valtype ] ->
    let value   = Construct.il_to_value   val_    in
    let valtype = Construct.il_to_valtype valtype in
    boolE (RI.Match.match_valtype [] (RI.Value.type_of_value value) valtype)
  | _ -> error no ("Wrong number/type of arguments to $Val_ok.")

(* $Ref_ok : store -> ref -> reftype *)
and ref_ok args = todo "ref_ok"


(*
(* Rule `Expand` has been compiled to `$expanddt` in animation.ml *)
let expand = function
  | [ v ] ->
    (try
      v
      |> Construct.al_to_deftype
      |> Types.expand_deftype
      |> Construct.al_of_comptype
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Expand" vs
*)


let rec il_hostcall = {
  name = "hostcall";
  f =
    function
    | [hostfunc; s; args] ->
      (match match_caseE "hostfunc" hostfunc with
      | [["_HOSTFUNC"]; []], [{it = TextE fname; _}] ->
        let vs = elts_of_list args in
        let s', result = call_hostfunc fname s vs in
        mk_singleton (mk_case (t_var "hostcallresult") [["RES"];[];[]] [s'; result])
      | _ -> error_value ("Not a hostfunc") hostfunc
      )
    | vs -> error_values ("Args to $hostcall") vs
}


(* Built-in functions (meta.spectec) *)


and il_use_step = {
  name = "use_step";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step")
      | None -> boolE false
      )
    | es -> error_values ("Args to $use_step") es
}
and il_use_step_pure = {
  name = "use_step_pure";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step_pure")
      | None -> boolE false
      )
    | es -> error_values ("Args to $use_step_pure") es
}
and il_use_step_read = {
  name = "use_step_read";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolE (rel_name = "Step_read")
      | None -> boolE false
      )
    | es -> error_values ("Args to $use_step_read") es
}
and il_use_step_ctxt = {
  name = "use_step_ctxt";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseE "instr" instr in
      List.mem (List.hd (List.hd mixop)) ["LABEL_"; "FRAME_"; "HANDLER_"] |> boolE
    | es -> error_values ("Args to $use_step_ctxt") es
}


and il_dispatch_step = {
  name = "dispatch_step";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step" -> il_call_func !il_env (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step") es
}
and il_dispatch_step_pure = {
  name = "dispatch_step_pure";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_pure" -> il_call_func !il_env (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step_pure rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step_pure") es
}
and il_dispatch_step_read = {
  name = "dispatch_step_read";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseE "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_read" -> il_call_func !il_env (rel_name ^ "/" ^ rule_name) [expA arg]
      | _ -> error instr.at ("No $Step_read rule for instr" ^ string_of_exp instr)
      )
    | es -> error_values ("Args to $dispatch_step_read") es
}

and il_step_read_throw_ref_handler = {
  name = "Step_read_throw_ref_handler";
  f =
    function
    | [arg] -> il_call_func !il_env "Step_read/throw_ref" [expA arg]
}

and il_builtin_list : il_builtin list = [
  il_use_step; il_use_step_pure; il_use_step_read; il_use_step_ctxt;
  il_dispatch_step; il_dispatch_step_pure; il_dispatch_step_read;
  il_step_read_throw_ref_handler; il_hostcall;
  ]

and il_builtins_mem fname =
  List.exists (fun builtin -> get_il_builtin_name builtin = fname) il_builtin_list

and il_call_builtins fname args : exp =
  match List.find_opt (fun numerics -> get_il_builtin_name numerics = fname) il_builtin_list with
  | Some il_builtin ->
    let args' = List.map (fun a -> match a.it with
    | ExpA e -> e
    | _ -> raise (Failure ("Wrong argument to builtin function " ^ fname ^ ": " ^ string_of_arg a))
    ) args in
    il_builtin.f args'
  | None -> raise (Failure ("Unknown builtin: " ^ fname))


and il_call_func env name args : exp =
  print_endline ("$ calling " ^ name ^ " with args: " ^ string_of_args args);
  match name with
  (* Hardcoded functions defined in meta.spectec *)
  | "Steps"  -> il_call_func env "steps"    args
  | "Step"   -> il_call_func env "step"     args
  (* Hardcoded functions defined in the compiler. *)
  | "Module_ok"     -> module_ok     args
  | "Externaddr_ok" -> externaddr_ok args
  | "Ref_ok"        -> ref_ok        args
  | "Val_ok"        -> val_ok        args
  (* Others *)
  | _ ->
    let builtin_name, is_builtin =
      match Il.Env.find_func_hint env name "builtin" with
      | None -> (name, false)
      | Some hint ->
        match hint.hintexp.it with
        | SeqE []     -> (name , true)  (* hint(builtin) *)
        | TextE fname -> (fname, true)  (* hint(builtin "g") *)
        | _ -> error no (sprintf "Ill-formed builtin hint for definition `%s`." name)
    in
    (match Def.find_dl_func_def name !dl with
    (* Regular function definition. *)
    | Some fdef when not is_builtin ->
      let (id, _ps, t, clauses, _) = fdef.it in
      let args' = List.map (Il.Eval.reduce_arg env) args in
      assert (id.it = name);
      (match Il.Eval.reduce_exp_call env id args' fdef.at clauses with
      | None -> error no (name ^ " failed to reduce: args' = " ^ string_of_args args')
      | Some e -> e
      )
    (* Builtins and numerics *)
    | Some { it = (_, _, _, [], _); at; _ } when is_builtin ->
      if Numerics.mem builtin_name then
        Numerics.call_numerics builtin_name args
      else if il_builtins_mem builtin_name then
        il_call_builtins builtin_name args
      else
        error no (sprintf "Builtin function `%s` is not defined in the interpreter." name)
    | _ when is_builtin ->
      error no (sprintf "Function `%s` is marked as builtin but there is either no declaration or is defined in SpecTec." name)
    | None -> error no (sprintf "There is no function named `%s`." name)
    )


(* Wasm interpreter entry *)


let setup_il_eval () : unit =
  Il.Eval.reduce_fncall_hook := fun env _ _ id args -> il_call_func env id.it args


let instantiate (args: arg list) : exp =
  let r = il_call_func !il_env "instantiate" args in
  print_endline ("$instantiate get: " ^ string_of_exp r);
  if Il.Eval.is_normal_exp r then r
  else
    raise (Failure "`instantiate` failed to run.")

let invoke (args: arg list) : exp =
  let r = il_call_func !il_env "invoke" args in
  print_endline ("$invoke get: " ^ string_of_exp r);
  if not (Il.Eval.is_normal_exp r)
  then
    raise (Failure "`invoke` failed to run.")
  else
    let r' = il_call_func !il_env "steps" [expA r] in
    print_endline ("$steps get: " ^ string_of_exp r');
    if Il.Eval.is_normal_exp r' then r'
    else raise (Failure "The result of `invoke` failed to reduce.")
