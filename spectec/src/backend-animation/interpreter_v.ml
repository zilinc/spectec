open Il_util
open Construct_v
open Def
open State_v
open Value
open Util
open Lib.Time
open Lib.Fun
open Error
open Il.Ast
open Il.Print
open Source
open Printf
open Il2al.Free
module HS = State_v.HostState
module A  = Al.Ast
module I  = Backend_interpreter
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
      "log";
      ]


let error at msg = Error.error at "animation/interpreter_v" msg
let error_np msg = error no_region msg

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


type builtin = { name : string; f : value list -> value OptMonad.m }

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
                   "  ▹ value: " ^ string_of_value rhs);
  fail ()

let string_of_exp exp = Il.Print.string_of_exp exp |> Lib.String.shorten
let string_of_arg arg = Il.Print.string_of_arg arg |> Lib.String.shorten
let string_of_args = function
  | [] -> ""
  | as_ -> "(" ^ concat ", " (List.map string_of_arg as_) ^ ")"

(* Environments *)

module VContext = struct
  module Map = Map.Make(String)
  type t = value Map.t

  let empty : t = Map.empty

  let add_varid ctx (s: id) (v: value) = Map.add s.it v ctx
  let find_varid ctx (s : id) : value = Map.find s.it ctx
  let dom_varid ctx : Set.t = ctx |> Map.bindings |> List.map fst |> Set.of_list
end


let dl : dl_def list ref = ref []
let il_env : Il.Env.t ref = ref Il.Env.empty


(** [lhs] is the pattern, and [rhs] is the expression. *)
let rec assign ctx (lhs: exp) (rhs: value) : VContext.t OptMonad.m =
  match lhs.it, rhs with
  | VarE name, _ ->
    VContext.add_varid ctx name rhs |> return
  | IterE ({ it = VarE x1; _ }, ((List|List1), [(x2, lhs')])), ListV _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs
  | IterE ({ it = VarE x1; _ }, (Opt, [x2, lhs'])), _ when Il.Eq.eq_id x1 x2 ->
    assign ctx lhs' rhs
  | IterE (e, (Opt, xes)), _ ->
    assert false  (* Animation shouldn't output this. *)
  | IterE (e, ((ListN _|List|List1) as iter, xes)), ListV vs ->
    let* ctxs = mapM (assign VContext.empty e) (Array.to_list !vs) in
    (* Assign length variable *)
    let* ctx' =
      match iter with
      | ListN (expr, None) ->
        let length = vl_of_nat (Array.length !vs) in
        assign ctx expr length
      | ListN _ ->
        fail ()
      | _ -> return ctx
    in
    foldlM (fun ctx (x, e) ->
      let vs = List.map (Fun.flip VContext.find_varid x) ctxs in
      let v = match iter with
      | Opt -> optV (List.nth_opt vs 0)
      | _   -> listV_of_list vs
      in
      assign ctx e v
    ) ctx' xes
  | TupE lhs_s, TupV rhs_s when List.length lhs_s = List.length rhs_s ->
    foldlM (fun c (p, e) -> assign c p e) ctx (List.combine lhs_s rhs_s)
  | CaseE (lhs_tag, lhs_s), CaseV (rhs_tag, rhs_s) ->
    begin match lhs_s.it with
    | TupE lhs_s' ->
      if vl_of_mixop lhs_tag = rhs_tag && List.length lhs_s' = List.length rhs_s then
        foldlM (fun c (p, e) -> assign c p e) ctx (List.combine lhs_s' rhs_s)
      else
        fail ()
    | _ -> fail ()
    end
  | OptE (Some lhs'), OptV (Some rhs'') -> assign ctx lhs' rhs''
  | CvtE (e1, nt, _), NumV n ->
    (match Xl.Num.cvt nt n with
    | Some n' -> assign ctx e1 (NumV n')
    | None -> fail ()
    )
  | SubE (p, t1, t2), CaseV (mixop, vs) ->
    let tcs = as_variant_typ !il_env t1 in
    (match List.find_map (fun (mixop', _, _) -> if vl_of_mixop mixop' = mixop then Some mixop' else None) tcs with
    | Some mixop' -> assign ctx p rhs
    | None -> fail ()
    )
  | _, _ -> fail ()


and is_value : exp -> bool = Il.Eval.is_normal_exp
and is_hnf   : exp -> bool = Il.Eval.is_head_normal_exp

and eval_exp ctx exp : value OptMonad.m =
  let open Xl in
  match exp.it with
  | VarE v -> (match VContext.Map.find_opt v.it ctx with
              | Some v' -> return v'
              | None -> error exp.at (sprintf "Variable `%s` is not in the value context.\n  ▹ vctx: %s" v.it
                                       (string_of_varset (VContext.dom_varid ctx)))
              )
  | BoolE b -> BoolV b |> return
  | NumE  n -> NumV  n |> return
  | TextE s -> TextV s |> return
  | UnE (op, _, e1) ->
    let* v1 = eval_exp ctx e1 in
    (match op, v1 with
    | #Bool.unop as op', BoolV b1 -> boolV (Bool.un op' b1) |> return
    | #Num.unop  as op', NumV  n1 ->
      (match Num.un op' n1 with
      | Some v -> NumV v |> return
      | None -> error_eval "Numeric unary expression" exp None
      )
    | _ -> error_eval "Unary expression" exp None
    )
  | BinE (op, ot, e1, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    (match op with
    | #Bool.binop as op' ->
      (match Bool.bin_partial op' v1 v2 of_bool_value boolV with
      | Some v -> return v
      | None -> error_eval "Boolean binary expression" exp None
      )
    | #Xl.Num.binop as op' ->
      (match Num.bin_partial op' v1 v2 of_num_value numV with
      | Some v -> return v
      | None -> error_eval "Numeric binary expression" exp None
      )
    )
  | CmpE (op, ot, e1, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    (match op, v1, v2 with
    | `EqOp, _, _ -> boolV (eq_value v1 v2)
    | `NeOp, _, _ -> boolV (eq_value v1 v2 |> not)
    | #Num.cmpop as op', NumV n1, NumV n2 ->
      (match Num.cmp op' n1 n2 with
      | Some b -> boolV b
      | None -> error_eval "Numeric comparison expresion" exp None
      )
    | _ -> error_eval "Comparison expression" exp None
    ) |> return
  | IdxE (e1, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    (match v1, v2 with
    | ListV vs, NumV (`Nat i) ->
      if i < Z.of_int (Array.length !vs) then
        Array.get !vs (Z.to_int i) |> return
      else
        error_eval "Indexing expression" exp
          (Some ("Index out-of-range:\n" ^
                 "seq   = " ^ string_of_value v1 ^ "\n" ^
                 "|seq| = " ^ string_of_int (Array.length !vs) ^ "\n" ^
                 "idx   = " ^ string_of_int (Z.to_int i)
                )
          )
    | _ -> error_eval "Indexing expression" exp
             (Some ("seq = " ^ string_of_value v1 ^ "; idx = " ^ string_of_value v2))
    )
  | SliceE (e1, e2, e3) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    let* v3 = eval_exp ctx e3 in
    (match v1, v2, v3 with
    | ListV vs, NumV (`Nat i), NumV (`Nat n) ->
      if Z.(i + n) <= Z.of_int (Array.length !vs) then
        ListV (Array.sub !vs (Z.to_int i) (Z.to_int n) |> ref) |> return
      else
        error_eval "Slicing expression" exp
          (Some ("|es| = " ^ string_of_int (Array.length !vs) ^
                 "; i = " ^ string_of_int (Z.to_int i) ^
                 "; n = " ^ string_of_int (Z.to_int n)))
    | _ -> error_eval "Slicing expression" exp
             (Some (string_of_value v1 ^ "[" ^ string_of_value v2 ^ ":" ^ string_of_value v3 ^ "]"))
    )
  | UpdE (e1, p, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    eval_path exp.at ctx v1 p
      (fun v p' ->
        if p'.it = RootP
        then return v2
        else error_eval "Sequence update expression" exp None
      )
  | ExtE (e1, p, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    eval_path exp.at ctx v1 p
      (fun v p' ->
        match v, v2, p'.it with
        | ListV vs, ListV vs2, RootP ->
          listV (Array.append !vs !vs2) |> return
        | _ -> error_eval "Sequence extension expression" exp None
      )
  | StrE vfs -> let* vfs' = mapM (eval_expfield ctx) vfs in StrV vfs' |> return
  | DotE (e1, atom) ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | StrV vfs -> !(snd (List.find (fun (atomN, _) -> atomN = Xl.Atom.to_string atom) vfs)) |> return
    | _ -> error_eval "Struct dot expression" exp None
    )
  | CompE (e1, e2) ->
    (* TODO(4, rossberg): avoid overlap with CatE? *)
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    compose exp.at v1 v2
  | MemE (e1, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    (match v2 with
    | OptV None -> boolV false
    | OptV (Some v2') -> boolV (eq_value v1 v2')
    | ListV vs2 -> boolV (Array.exists (eq_value v1) !vs2)
    | _ -> error_eval "Membership expression" exp None
    ) |> return
  | LenE e1 ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | ListV vs -> vl_of_nat (Array.length !vs) |> return
    | _ -> error_eval "Sequence length expression" exp None
    )
  | TupE es -> let* vs = mapM (eval_exp ctx) es in TupV vs |> return
  | CallE (fid, args) ->
    let* args' = mapM (eval_arg ctx) args in
    call_func fid.it args'
  | IterE (e1, ((_, xes) as iterexp)) ->
    let* (iter', xvs) as iterval = eval_iterexp ctx iterexp in
    let ids, vs = List.split xvs in
    if iter' <= List1 && vs = [] then
      error_eval "Iterated expression" exp (Some "Inadequate information about the iteration scheme.")
    else
      (match iter' with
      | Opt ->
        let ovs = List.map as_opt_value vs in
        if List.for_all Option.is_none ovs then
          OptV None |> return
        else if List.for_all Option.is_some ovs then
          let vs1 = List.map Option.get ovs in
          let* ctx' = foldlM (fun c (a, b) ->
            VContext.add_varid c a b |> return
          ) ctx (List.combine ids vs1) in
          let* v1 = eval_exp ctx' e1 in
          OptV (Some v1) |> return
        else
          error_eval "Iterated epxression" exp (Some "?-iterator inflow expressions don't match.")
      | List | List1 ->
        let n = Array.length (!(as_list_value (List.hd vs))) in
        if iter' = List || n >= 1 then
          let en = NumE (`Nat (Z.of_int n)) $$ exp.at % (NumT `NatT $ exp.at) in
          eval_exp ctx (IterE (e1, (ListN (en, None), xes)) $> exp)
        else
          error_eval "Iterated expression" exp (Some "Using +-iterator but sequence length is 0")
      | ListN (NumV (`Nat n'), oi) ->
        let vss = List.map as_list_value vs in
        let ns = List.map (fun vs -> Array.length !vs) vss in
        let n = Z.to_int n' in
        if List.for_all ((=) n) ns then
          let* vs1 = mapM (fun i ->
            let vsI = List.map (fun vs -> Array.get !vs i) vss in
            let ctx' = List.fold_left2 VContext.add_varid ctx ids vsI in
            let ctx'' =
              Option.fold oi ~none:ctx' ~some:(fun id ->
                let vn = NumV (`Nat (Z.of_int i)) in
                VContext.add_varid ctx' id vn
              )
            in eval_exp ctx'' e1
          ) (0 -- n)
          in
          listV_of_list vs1 |> return
        else
          error_eval "Iterated expression" exp (Some "Inflow sequences don't agree on the length")
      | ListN _ -> error_eval "Iterated expression" exp None
      )
  | ProjE (e1, i) ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | TupV vs -> List.nth vs i |> return
    | _ -> error_eval "Tuple projection expression" exp None
    )
  | UncaseE (e1, mixop) ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | CaseV (mixop', vs) ->
      if Value.vl_of_mixop mixop = mixop' then
        return (TupV vs)
      else
        error_eval "Constructor unwrapping expression" exp
                   (Some ("mixop = " ^ string_of_mixop mixop ^ "; mixop' = " ^ Value.string_of_mixop mixop'))
    | _ -> error_eval "Constructor unwrapping expression" exp
                      (Some ("e1 ⤳ " ^ string_of_value v1 ^ "; mixop = " ^ string_of_mixop mixop))
    )
  | OptE oe1 -> let* ov1 = opt_mapM (eval_exp ctx) oe1 in OptV ov1 |> return
  | TheE e1 ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | OptV (Some v11) -> return v11
    | _ -> error_eval "THE expression" exp None
    )
  | ListE es -> let* vs = mapM (eval_exp ctx) es in listV (Array.of_list vs) |> return
  | LiftE e1 ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | OptV None -> ListV (ref [||])
    | OptV (Some v11) -> ListV (ref [|v11|])
    | _ -> error_eval "Option lifting expression" exp None
    ) |> return
  | CatE (e1, e2) ->
    let* v1 = eval_exp ctx e1 in
    let* v2 = eval_exp ctx e2 in
    (match v1, v2 with
    | ListV vs1, ListV vs2 -> ListV (ref (Array.append !vs1 !vs2))
    | OptV None, OptV _ -> v2
    | OptV _, OptV None -> v1
    | _ -> error_eval "Sequence concatenation expression" exp None
    ) |> return
  | CaseE (op, e1) ->
    (match e1.it with
    | TupE es -> let* vs = mapM (eval_exp ctx) es in CaseV (vl_of_mixop op, vs) |> return
    | _ -> let* v = eval_exp ctx e1 in CaseV (vl_of_mixop op, [v]) |> return
    )
  | CvtE (e1, _nt1, nt2) ->
    let* v1 = eval_exp ctx e1 in
    (match v1 with
    | NumV n ->
      (match Num.cvt nt2 n with
      | Some n' -> NumV n' |> return
      | None -> error_eval "Numeric type conversion" exp (Some "Cannot perform conversion.")
      )
    | _ -> error_eval "Numeric type conversion" exp (Some ("Not a numeric:" ^ string_of_exp e1))
    )
  | SubE (e1, t1, t2) -> eval_exp ctx e1


and eval_iter ctx = function
  | Opt   -> return Value.Opt
  | List  -> return Value.List
  | List1 -> return Value.List1
  | ListN (e, oi) ->
    let* v = eval_exp ctx e in
    Value.ListN (v, oi) |> return

and eval_iterexp ctx (iter, xes) : (Value.iter * (id * value) list) OptMonad.m =
  let* iter' = eval_iter ctx iter in
  let excl_ids = match iter with
  | ListN(_, Some i) -> [i.it]
  | _ -> []
  in
  (* Remove the outflowing binding. *)
  let xes' = List.filter (fun (x, e) -> List.mem x.it excl_ids |> not) xes in
  let* xes'' = mapM (fun (id, e) -> let* v = eval_exp ctx e in return (id, v)) xes' in
  return (iter', xes'')

and compose at v1 v2 : value OptMonad.m =
  (match v1, v2 with
  | ListV vs1, ListV vs2 -> listV (Array.append !vs1 !vs2) |> return
  | OptV None, OptV _ -> return v2
  | OptV _, OptV None -> return v1
  | StrV vfs1, StrV vfs2 ->
    let merge (atom1, v1) (atom2, v2) =
      assert (atom1 = atom2);
      let* v12 = compose at !v1 !v2 in
      return (atom1, ref v12)
    in
    let* vfs12 = mapM (Lib.Fun.uncurry merge) (List.combine vfs1 vfs2) in
    StrV vfs12 |> return
  | _ -> error at ("Composition error: \n" ^
                   " ▹ v1 = " ^ string_of_value v1 ^ "\n" ^
                   " ▹ v2 = " ^ string_of_value v2 ^ ".")
  )

and eval_expfield ctx (atom, e) : (string * value ref) OptMonad.m =
  let* v = eval_exp ctx e in return (Xl.Atom.to_string atom, ref v)

and eval_path at ctx v p (f: value -> path -> value OptMonad.m) : value OptMonad.m =
  match p.it with
  | RootP -> f v p
  | IdxP (p1, e1) ->
    let* v1 = eval_exp ctx e1 in
    let f' v' p1' =
      match v', v1 with
      | ListV vs, NumV (`Nat i) when i < Z.of_int (Array.length !vs) ->
        let* vs' = mapiM (fun j vJ -> if Z.of_int j = i then f vJ p1' else return vJ) (Array.to_list !vs) in
        listV_of_list vs' |> return
      | _ -> error at ("Index path failed to evaluate:\n" ^
                       "  ▹ v: " ^ string_of_value v ^ "\n" ^
                       "  ▹ p: " ^ string_of_path p)
    in
    eval_path at ctx v p1 f'
  | SliceP (p1, e1, e2) ->
    let* vi = eval_exp ctx e1 in
    let* vn = eval_exp ctx e2 in
    let f' v p1' =
      match v, vi, vn with
      | ListV vs, NumV (`Nat i), NumV (`Nat n) when Z.(i + n) < Z.of_int (Array.length !vs) ->
        let vs1 = Array.sub !vs 0 (Z.to_int i) in
        let v2  = listV (Array.sub !vs (Z.to_int i) (Z.to_int n)) in
        let vs3 = Array.sub !vs Z.(to_int (i + n)) (Array.length !vs - Z.to_int Z.(i + n)) in
        let* v2' = f v2 p1' in
        (match v2' with
        | ListV vs2 -> listV (Array.append (Array.append vs1 !vs2) vs3) |> return
        | _ -> assert false
        )
      | _ -> error at ("Slice path failed to evaluate:\n" ^
                       "  ▹ v: " ^ string_of_value v ^ "\n" ^
                       "  ▹ p: " ^ string_of_path p)
    in
    eval_path at ctx v p1 f'
  | DotP (p1, atom) ->
    let f' v p1' =
      match v with
      | StrV vfs ->
        let* vfs' = mapM (fun (atomI, vI) ->
          if atomI = Xl.Atom.to_string atom
          then let* vI' = f !vI p1' in return (atomI, ref vI')
          else return (atomI, vI)
        ) vfs in
        StrV vfs' |> return
      | _ -> error at ("Dot path failed to evaluate:\n" ^
                       "  ▹ v: " ^ string_of_value v ^ "\n" ^
                       "  ▹ p: " ^ string_of_path p)
    in
    eval_path at ctx v p1 f'

and eval_arg ctx a : Value.arg OptMonad.m =
  match a.it with
  | ExpA  e  -> let* v = eval_exp ctx e in valA v |> return
  | TypA t  -> return (Value.TypA t)  (* types are reduced on demand *)
  | DefA id -> return (Value.DefA id)
  | GramA g -> return (Value.GramA g)

and eval_prem ctx prem : VContext.t OptMonad.m =
  match prem.it with
  | ElsePr -> return ctx
  | LetPr (lhs, rhs, _vs) ->
    let* rhs' = eval_exp ctx rhs in
    assign ctx lhs rhs'
  | IfPr e ->
    let* b = eval_exp ctx e in
    if b = boolV true then return ctx
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
      let* n' = eval_exp ctx n <&> as_nat_value in
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
          let vx_star = ListV (ref [||]) in
          VContext.add_varid ctx x_star vx_star
        | _ -> assert false
      ) ctx out_binds in
      (* Run the loop *)
      let* ctx'' = foldlM (fun ctx idx ->
        let lctxr = ref ctx in
        lctxr := VContext.add_varid !lctxr i (vl_of_nat idx);
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
            let vx_star = VContext.Map.find_opt x_star.it !lctxr |> Option.get in
            let vs = as_list_value vx_star in
            let vx_star' = listV (Array.append !vs ([|vx|])) in
            lctxr := VContext.add_varid !lctxr x_star vx_star'
          | _ -> assert false
        ) out_binds;
        return !lctxr
      ) ctx' (0 -- Z.to_int n') in
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
      let* in_vals = mapM (fun (x, e) -> let* v = eval_exp ctx e in return (x, v)) in_binds in
      assert (List.length in_vals > 0);
      let run_opt = match List.hd in_vals |> snd with
      | OptV None     -> false
      | OptV (Some _) -> true
      | _ -> assert false
      in
      (* Check that all inputs agree. *)
      List.iter (fun (_, opt_val) ->
        match opt_val, run_opt with
        | OptV None, false -> ()
        | OptV (Some _), true -> ()
        | _ -> assert false
      ) in_vals;
      let* ctx' = begin if not run_opt then
      (* When the optional is None, all outflow variables should be None. *)
        List.fold_left (fun ctx (x, e) ->
          match e.it with
          | VarE x_question -> VContext.add_varid ctx x_question none
          | _ -> assert false
        ) ctx out_binds |> return
      else
      (* When the optional is Some *)
        let lctxr = ref ctx in
        (* In-flow *)
        List.iter (fun (x, opt_val) ->
          let OptV (Some val_) = opt_val in
          lctxr := VContext.add_varid !lctxr x val_
        ) in_vals;
        let* lctx = eval_prems !lctxr prems in
        lctxr := lctx;
        (* Out-flow *)
        List.iter (fun (x, e) ->
          match e.it with
          | VarE x_question ->
            let vx = VContext.find_varid !lctxr x in
            let opt_vx_question = VContext.Map.find_opt x_question.it !lctxr in
            begin match opt_vx_question with
            | Some vx_question -> assert false
            | None -> let some_vx = some vx in
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
  | VarT (pid, []), _ -> return ctx  (* FIXME(zilinc): Do we need to do anything here for poly-functions? *)
  | _ -> fail ()

and match_arg ctx at (pat: arg) (arg: Value.arg) : VContext.t OptMonad.m =
  match pat.it, arg with
  | TypA ptyp , Value.TypA atyp -> match_typ ctx at ptyp atyp
  | ExpA pexp , Value.ValA aval -> assign ctx pexp aval
  | DefA pid  , Value.DefA _    -> todo "match_arg DefA"
  | GramA psym, Value.GramA _   -> todo "match_arg GramA"
  | _ -> fail ()


and match_args ctx at pargs args : VContext.t OptMonad.m =
  match pargs, args with
  | [], [] -> return ctx
  | parg::pargs', arg::args' ->
    let* ctx'  = match_arg ctx at parg arg in
    let* ctx'' = match_args ctx' at pargs' args' in
    return ctx''

and match_clause at (fname: string) (nth: int) (clauses: clause list) (args: Value.arg list) : value OptMonad.m =
  match clauses with
  | [] -> fail ()
  | cl :: cls ->
    let DefD (binds, pargs, exp, prems) = cl.it in
    let old_env = !il_env in
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
    il_env := old_env;
    return val_


and eval_func name func_def args : value OptMonad.m =
  let (_, params, typ, fcs, _) = func_def.it in
  match_clause no_region name 1 fcs args

and call_func name args =
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
      if Numerics_v.mem builtin_name then
        Numerics_v.call_numerics builtin_name args |> return
      else if builtins_mem builtin_name then
        call_builtins builtin_name args
      else if builtin_name = "hostcall" then
        hostcall args
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
  let as_const ty = function
  | CaseV ([["CONST"];[];[]], [CaseV ([[ty']], []); n])
  | OptV (Some (CaseV ([["CONST"];[];[]], [CaseV ([[ty']], []); n]))) when ty = ty' -> n
  | v -> error no ("Host function call: Not " ^ ty ^ ".CONST: " ^ string_of_value v)
  in
  let argc = List.length vs in
  let print_eff s = HS.Print s in
  let effs = (match name with
  | "print" when argc = 0 -> [ print_eff "- print: ()\n" ]
  | "print_i32" when argc = 1 ->
    List.hd vs
    |> as_const "I32"
    |> vl_to_uN_32
    |> RI.I32.to_string_s
    |> Printf.sprintf "- print_i32: %s\n"
    |> print_eff
    |> fun e -> [e]
  | "print_i64" when argc = 1 ->
    List.hd vs
    |> as_const "I64"
    |> vl_to_uN_64
    |> RI.I64.to_string_s
    |> Printf.sprintf "- print_i64: %s\n"
    |> print_eff
    |> fun e -> [e]
  | "print_f32" when argc = 1 ->
    List.hd vs
    |> as_const "F32"
    |> vl_to_float32
    |> RI.F32.to_string
    |> Printf.sprintf "- print_f32: %s\n"
    |> print_eff
    |> fun e -> [e]
  | "print_f64" when argc = 1 ->
    List.hd vs
    |> as_const "F64"
    |> vl_to_float64
    |> RI.F64.to_string
    |> Printf.sprintf "- print_f64: %s\n"
    |> print_eff
    |> fun e -> [e]
  | "print_i32_f32" when argc = 2 ->
    let [v1; v2] = vs in
    let i32 = v1 |> as_const "I32" |> vl_to_nat32   |> RI.I32.to_string_s in
    let f32 = v2 |> as_const "F32" |> vl_to_float32 |> RI.F32.to_string   in
    Printf.sprintf "- print_i32_f32: %s %s\n" i32 f32 |> print_eff |> fun e -> [e]
  | "print_f64_f64" when argc = 2 ->
    let [v1; v2] = vs in
    let f64  = v1 |> as_const "F64" |> vl_to_float64 |> RI.F64.to_string in
    let f64' = v2 |> as_const "F64" |> vl_to_float64 |> RI.F64.to_string in
    Printf.sprintf "- print_f64_f64: %s %s\n" f64 f64' |> print_eff |> fun e -> [e]
  | name -> error no ("Invalid host function call: " ^ name)
  )
  in
  let get_hoststate store : value =
    let store' = as_str_value store in
    Record.find "HOST" store'
  in
  let set_hoststate hs store : value =
    let store' = as_str_value store |> List.map (fun (k, v) -> (k, ref !v)) in  (* Record.clone is not adequate. *)
    Record.replace "HOST" hs store';
    StrV store'
  in
  let hs' = HS.inc_timestamp (get_hoststate s) in
  let s' = set_hoststate hs' s in
  let hostcallresult = caseV [["RES"];[];[]] [s'; caseV [["_VALS"];[]] [listV [||]]] in
  let res = [ hostcallresult ] |> listV_of_list in
  (res, effs)

and hostcall : Value.arg list -> value OptMonad.m = function
  | [ ValA name; ValA s; ValA val_ ] ->
    let name' = (match name with
    | CaseV ([["_HOSTFUNC"];[]], [hf]) -> as_text_value hf
    | _ -> error no ("Not a hostfunc")
    )
    in
    let glb_hs = HS.get_glb_state () in
    let lcl_hs = as_str_field "HOST" s in
    let vals = as_list_value' val_ in
    (match HS.chk_state lcl_hs with
    | Earlier ->
      (* Host function has been called already. Look up the effect registry. *)
      (match HS.lookup_effect name' (HS.get_timestamp lcl_hs) with
      | Some (res, _effs) -> return res
      | None -> error no ("No such entry in effect resgistry.")
      )
    | Good ->
      let res, effs = call_hostfunc name' s vals in
      HS.add_effects name' res effs;
      return res
    | Later -> error no ("Host function `" ^ name' ^ "` is calling into the future.")
    )
  | _ -> error no ("Invalid arguments to $hostcall")


(*
and hostcall = {
  name = "hostcall";
  f =
    function
    | [hostfunc; s; args] ->
      (match match_caseV "hostfunc" hostfunc with
      | [["_HOSTFUNC"]; []], [TextV fname] ->
        let vs = as_list_value' args in
        let s', result = call_hostfunc fname s vs in
        listV [| caseV [["RES"];[];[]] [s'; result] |] |> return
      | _ -> error_value ("Not a hostfunc") hostfunc
      )
    | vs -> error_values ("Args to $hostcall") vs
}
*)

(* Built-in functions (meta.spectec) *)

and use_step : builtin = {
  name = "use_step";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolV (rel_name = "Step") |> return
      | None -> BoolV false |> return
      )
    | vs -> error_values ("Args to $use_step") vs
}
and use_step_pure = {
  name = "use_step_pure";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> BoolV (rel_name = "Step_pure") |> return
      | None -> BoolV false |> return
      )
    | vs -> error_values ("Args to $use_step_pure") vs
}
and use_step_read = {
  name = "use_step_read";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, _, _) -> boolV (rel_name = "Step_read") |> return
      | None -> boolV false |> return
      )
    | vs -> error_values ("Args to $use_step_read") vs
}
and use_step_ctxt = {
  name = "use_step_ctxt";
  f =
    function
    | [instr] ->
      let mixop, _ = match_caseV "instr" instr in
      List.mem (List.hd (List.hd mixop)) ["LABEL_"; "FRAME_"; "HANDLER_"] |> boolV |> return
    | vs -> error_values ("Args to $use_step_ctxt") vs
}


and dispatch_step = {
  name = "dispatch_step";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step" -> call_func (rel_name ^ "/" ^ rule_name) [valA arg]
      | _ -> error no ("No $Step rule for instr" ^ string_of_value instr)
      )
    | vs -> error_values ("Args to $dispatch_step") vs
}
and dispatch_step_pure = {
  name = "dispatch_step_pure";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_pure" -> call_func (rel_name ^ "/" ^ rule_name) [valA arg]
      | _ -> error no ("No $Step_pure rule for instr" ^ string_of_value instr)
      )
    | vs -> error_values ("Args to $dispatch_step_pure") vs
}
and dispatch_step_read = {
  name = "dispatch_step_read";
  f =
    function
    | [instr; arg] ->
      let mixop, _ = match_caseV "instr" instr in
      (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
      | Some (rel_name, rule_name, _) when rel_name = "Step_read" -> call_func (rel_name ^ "/" ^ rule_name) [valA arg]
      | _ -> error no ("No $Step_read rule for instr" ^ string_of_value instr)
      )
    | vs -> error_values ("Args to $dispatch_step_read") vs
}

and step_read_throw_ref_handler = {
  name = "Step_read_throw_ref_handler";
  f =
    function
    | [arg] -> call_func "Step_read/throw_ref" [valA arg]
    | vs -> error_values ("Args to $Step_read/throw_ref") vs
}


and builtin_list : builtin list = [
  use_step; use_step_pure; use_step_read; use_step_ctxt;
  dispatch_step; dispatch_step_pure; dispatch_step_read;
  step_read_throw_ref_handler;
  ]

and call_builtins fname args : value OptMonad.m =
  match List.find_opt (fun numerics -> numerics.name = fname) builtin_list with
  | Some builtin ->
    let args' = List.map (function
    | ValA v -> v
    | a -> raise (Failure ("Wrong argument to builtin function " ^ fname ^ ": " ^ Value.string_of_arg a))
    ) args in
    builtin.f args'
  | None -> raise (Failure ("Unknown builtin: " ^ fname))

and builtins_mem fname =
  List.exists (fun builtin -> builtin.name = fname) builtin_list





(* Hard-coded relations *)


(* $Module_ok : module -> moduletype *)
and module_ok args : value =
  match args with
  | [ ValA module_ ] ->
    let module_' = vl_to_module module_ in
    let ModuleT (its, ets) = RI.Valid.check_module module_' in
    let importtypes = List.map (fun (RI.Types.ImportT (_, _, xt)) -> vl_of_externtype xt) its in
    let exporttypes = List.map (fun (RI.Types.ExportT (_,    xt)) -> vl_of_externtype xt) ets in
    caseV [[];["->"];[]] [ listV_of_list importtypes; listV_of_list exporttypes ]
  | _ -> error no ("Wrong number/type of arguments to $Module_ok.")

(* $Externaddr_ok : store -> externaddr -> externtype -> bool *)
and externaddr_ok = function
  | [ ValA s; ValA eaddr; ValA etype ] ->
    (match match_caseV "externaddr" eaddr with
    | [[name];[]], [NumV (`Nat z)] ->
      let addr = Z.to_int z in
      let externaddr_type =
        name^"S"
        |> Store.access
        |> as_list_value
        |> (!)
        |> Fun.flip Array.get addr
        |> as_str_field "TYPE"
        |> fun type_ -> caseV [[name];[]] [type_]
        |> vl_to_externtype
      in
      let externtype = vl_to_externtype etype in
      boolV (RI.Match.match_externtype [] externaddr_type externtype)
    | _ -> error_value "$Externaddr_ok (externaddr)" eaddr
    )
  | _ -> error no ("Wrong number/type of arguments to $Externaddr_ok.")

(* $Val_ok : store -> val -> valtype -> bool *)
and val_ok = function
  | [ ValA s; ValA val_; ValA valtype ] ->
    let value   = vl_to_value   val_    in
    let valtype = vl_to_valtype valtype in
    BoolV (RI.Match.match_valtype [] (RI.Value.type_of_value value) valtype)
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


(* Wasm interpreter entry *)

let instantiate (args: Value.arg list) : value =
  match call_func "instantiate" args |> run_opt with
  | Some v -> v
  | None -> raise (Failure "`instantiate` failed to run.")

let invoke (args: Value.arg list) : value =
  match (let* r = call_func "invoke" args in
         call_func "steps" [ValA r]) |> run_opt
  with
  | Some r' -> r'
  | None -> raise (Failure "`invoke` failed to run.")
