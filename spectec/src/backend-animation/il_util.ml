open Il
open Ast
open Eval
open Print
open Util
open Source

let error at msg = Error.error at "Il_util" msg


(* Predicate *)

let is_varE : exp -> bool = fun e ->
  match e.it with
  | VarE _ -> true
  | _      -> false

let is_unary_tupT : typ -> bool = fun t ->
  match t.it with
  | TupT [_] -> true
  | _        -> false

let is_unary_variantT : deftyp -> bool = fun deft ->
  match deft.it with
  | VariantT [_] -> true
  | _            -> false


(* Destruct *)


let il_to_nat e : Xl.Num.nat =
  match e.it with
  | NumE (`Nat n) -> n
  | _ -> error e.at ("Il expression not a nat: " ^ string_of_exp e)

let as_iter_typ env t : typ =
  match (reduce_typ env t).it with
  | IterT (t', (List | List1 | ListN _)) -> t'
  | _ -> error t.at ("Input type is not an iterated type: " ^ string_of_typ t)

let as_opt_typ env t : typ =
  match (reduce_typ env t).it with
  | IterT (t', Opt) -> t'
  | _ -> error t.at ("Input type is not an option type: " ^ string_of_typ t)

let as_iter_typ' iter env t : typ =
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

let find_str_field atom str : exp =
  match str.it with
  | StrE fes -> List.find (fun (atom', e) -> Xl.Atom.to_string atom' = atom) fes |> snd
  | _ -> error str.at ("Input expression is not a struct: " ^ string_of_exp str)

let find_list_elem p lst : exp =
  match lst.it with
  | ListE es -> List.find (fun e -> p e) es
  | _ -> error lst.at ("Input expression is not a list: " ^ string_of_exp lst)

let nth_of_list lst (idx: Z.t) : exp =
  match lst.it with
  | ListE es -> List.nth es (Z.to_int idx)
  | _ -> error lst.at ("Input expression is not a list: " ^ string_of_exp lst)

let args_of_case case : exp list =
  match case.it with
  | CaseE (_, tup) ->
    (match tup.it with
    | TupE es -> es
    | _ -> [tup]
    )
  | _ -> error case.at ("Input expression is not a case: " ^ string_of_exp case)

let text_to_string txt : string =
  match txt.it with
  | TextE str -> str
  | _ -> error txt.at ("Input expression is not a text: " ^ string_of_exp txt)

let of_bool_exp = function
  | BoolE b -> Some b
  | _ -> None

let of_num_exp = function
  | NumE n -> Some n
  | _ -> None



(* Construct *)

let no = no_region


(* Construct type *)

let natT ?(at = no) () = NumT `NatT $ at
let iterT ?(at = no) t : typ = IterT (t, List) $ at
let optT  ?(at = no) t : typ = IterT (t, Opt) $ at

let t_var ?(at = no) name : typ = VarT (name $ at, []) $ at
let t_app ?(at = no) name ts : typ = VarT (name $ at, ts) $ at
let t_star ?(at = no) name : typ = iterT (t_var name)
let t_list ?(at = no) name : typ = VarT ("list" $ at, [TypA (t_var name) $ at]) $ at
let t_opt  ?(at = no) name : typ = optT  (t_var name)
let rec t_tup  ?(at = no) ts : typ = TupT (List.map (fun t -> (varE ~note:t "_", t)) ts) $ at


(* Construct argument *)

and expA ?(at = no) e = ExpA e $ at
and typA ?(at = no) ty = TypA ty $ at
and defA ?(at = no) id = DefA id $ at


(* Construct expression *)

and mk_expr at note it = it $$ at % note

and varE ?(at = no) ~note v = VarE (v $ at) |> mk_expr at note
and boolE ?(at = no) b = BoolE b |> mk_expr at (BoolT $ at)
and numE ?(at = no) ~note i = NumE i |> mk_expr at note
and natE ?(at = no) i = NumE (`Nat i) |> mk_expr at (natT ())
and intE ?(at = no) i = NumE (`Int i) |> mk_expr at (NumT `IntT $ at)
and textE ?(at = no) s = TextE s |> mk_expr at (TextT $ at)
and cvtE ?(at = no) (e, nt1, nt2) = CvtE (e, nt1, nt2) |> mk_expr at (NumT nt2 $ at)
and caseE ?(at = no) ~note (mixop, es) = CaseE (mixop, es) |> mk_expr at note
and tupE ?(at = no) ~note el = TupE el |> mk_expr at note
and listE ?(at = no) t es : exp = mk_expr at t (ListE es)
and listE' ?(at = no) es : exp = match es with
  | [] -> error at "listE: can't infer type when []"
  | e::es' -> let t = iterT (e.note) in listE t es
and optE ?(at = no) t oe : exp = mk_expr at t (OptE oe)
and optE' ?(at = no) oe : exp = match oe with
  | None   -> error at "optE: can't infer type when None"
  | Some e -> let t = iterT (e.note) in optE t oe
and strE ?(at = no) ~note r = StrE r |> mk_expr at note
and subE ?(at = no) id t1 t2 = SubE (id, t1, t2) |> mk_expr at t2
(*
and unE ?(at = no) ~note (unop, t, e) = UnE (unop, t, e) |> mk_expr at note
and binE ?(at = no) ~note (binop, t, e1, e2) = BinE (binop, t, e1, e2) |> mk_expr at note
and updE ?(at = no) ~note (e1, pl, e2) = UpdE (e1, pl, e2) |> mk_expr at note
and extE ?(at = no) ~note (e1, pl, e2, dir) = ExtE (e1, pl, e2, dir) |> mk_expr at note
and compE ?(at = no) ~note (e1, e2) = CompE (e1, e2) |> mk_expr at note
and liftE ?(at = no) ~note e = LiftE e |> mk_expr at note
and catE ?(at = no) ~note (e1, e2) = CatE (e1, e2) |> mk_expr at note
and memE ?(at = no) ~note (e1, e2) = MemE (e1, e2) |> mk_expr at note
and lenE ?(at = no) ~note e = LenE e |> mk_expr at note
and callE ?(at = no) ~note (id, el) = CallE (id, el) |> mk_expr at note
and invCallE ?(at = no) ~note (id, il, el) = InvCallE (id, il, el) |> mk_expr at note
and iterE ?(at = no) ~note (e, ite) = IterE (e, ite) |> mk_expr at note
and optE ?(at = no) ~note e_opt = OptE e_opt |> mk_expr at note
and listE ?(at = no) ~note el = ListE el |> mk_expr at note
and getCurStateE ?(at = no) ~note () = GetCurStateE |> mk_expr at note
and getCurContextE ?(at = no) ~note e = GetCurContextE e |> mk_expr at note
and chooseE ?(at = no) ~note e = ChooseE e |> mk_expr at note
and isCaseOfE ?(at = no) ~note (e, a) = IsCaseOfE (e, a) |> mk_expr at note
and isValidE ?(at = no) ~note e = IsValidE e |> mk_expr at note
and contextKindE ?(at = no) ~note a = ContextKindE a |> mk_expr at note
and isDefinedE ?(at = no) ~note e = IsDefinedE e |> mk_expr at note
and matchE ?(at = no) ~note (e1, e2) = MatchE (e1, e2) |> mk_expr at note
and hasTypeE ?(at = no) ~note (e, ty) = HasTypeE (e, ty) |> mk_expr at note
and topValueE ?(at = no) ~note e_opt = TopValueE e_opt |> mk_expr at note
and topValuesE ?(at = no) ~note e = TopValuesE e |> mk_expr at note
and yetE ?(at = no) ~note s = YetE s |> mk_expr at note



and mk_path at it = Util.Source.($) it at

and idxP ?(at = no) e = IdxP e |> mk_path at
and sliceP ?(at = no) (e1, e2) = SliceP (e1, e2) |> mk_path at
and dotP ?(at = no) a = DotP a |> mk_path at

*)

and mk_nat ?(at = no) n : exp = natE (Z.of_int n)
and mk_int ?(at = no) n : exp = intE (Z.of_int n)

(* ASSUMES: [e] has numtype [t1]. *)
and mk_cvt ?(at = no) e t1 t2 : exp = if t1 = t2 then e else CvtE (e, t1, t2) $$ at % (NumT t2 $ at)

(* When e1 and e2 are both `NatT, we want to construct e1 - e2, with both of them
   converted to `IntT, and then convert the result back to `NatT.
*)
and mk_cvt_sub ?(at = no) e1 e2 : exp =
  let e1' = mk_cvt ~at:e1.at e1 `NatT `IntT in
  let e2' = mk_cvt ~at:e2.at e2 `NatT `IntT in
  let e = BinE (`SubOp, `IntT, e1', e2') $$ at % (NumT `IntT $ at) in
  mk_cvt e `IntT `NatT

and mk_atom ?(at = no) ~info (atom: string) : Xl.Atom.atom =
  Xl.Atom.(match atom with
  | "->" -> Arrow
  | _    -> Atom atom
  ) $$ at % info
  (*
  | Infinity                     (* infinity *)
  | Bot                          (* `_|_` *)
  | Top                          (* `^|^` *)
  | Dot                          (* `.` *)
  | Dot2                         (* `..` *)
  | Dot3                         (* `...` *)
  | Semicolon                    (* `;` *)
  | Backslash                    (* `\` *)
  | Mem                          (* `<-` *)
  | Arrow                        (* `->` *)
  | Arrow2                       (* ``=>` *)
  | ArrowSub                     (* `->_` *)
  | Arrow2Sub                    (* ``=>_` *)
  | Colon                        (* `:` *)
  | ColonSub                     (* `:_` *)
  | Sub                          (* `<:` *)
  | Sup                          (* `:>` *)
  | Assign                       (* `:=` *)
  | Equal                        (* ``=` *)
  | EqualSub                     (* ``=_` *)
  | NotEqual                     (* ``=/=` *)
  | Less                         (* ``<` *)
  | Greater                      (* ``>` *)
  | LessEqual                    (* ``<=` *)
  | GreaterEqual                 (* ``>=` *)
  | Equiv                        (* `==` *)
  | EquivSub                     (* `==_` *)
  | Approx                       (* `~~` *)
  | ApproxSub                    (* `~~_` *)
  | SqArrow                      (* `~>` *)
  | SqArrowSub                   (* `~>_` *)
  | SqArrowStar                  (* `~>*` *)
  | SqArrowStarSub               (* `~>*_` *)
  | Prec                         (* `<<` *)
  | Succ                         (* `>>` *)
  | Turnstile                    (* `|-` *)
  | TurnstileSub                 (* `|-_` *)
  | Tilesturn                    (* `-|` *)
  | TilesturnSub                 (* `-|_` *)
  | Quest                        (* ``?` *)
  | Plus                         (* ``+` *)
  | Star                         (* ``*` *)
  | Comma                        (* ``,` *)
  | Cat                          (* ``++` *)
  | Bar                          (* ``|` *)
  | BigAnd                       (* `(/\)` *)
  | BigOr                        (* `(\/)` *)
  | BigAdd                       (* `(+)` *)
  | BigMul                       (* `( * )` *)
  | BigCat                       (* `(++)` *)
  | LParen | RParen              (* ``(` `)` *)
  | LBrack | RBrack              (* ``[` `]` *)
  | LBrace | RBrace              (* ``{` `}` *)
  *)

and mk_mixop' ?(at = no) ~info (atom: string) arity : mixop =
  [mk_atom ~info atom] :: List.init arity (Fun.const [])

and mk_mixop ?(at = no) ~info (mixop: string list list) : mixop =
  List.map (fun as_ -> List.map (fun a -> mk_atom ~info a) as_) mixop

and mk_case' ?(at = no) tname mixop es : exp =
  let t = t_var tname in
  mk_case t mixop es

and mk_case ?(at = no) t mixop es : exp =
  let info = Xl.Atom.{def = ""; case = ""} in
  let mixop' = mk_mixop ~info:info mixop in
  let e = mk_tup es in
  caseE ~note:t (mixop', e)

and mk_nullary' ?(at = no) tname con : exp =
  mk_case' tname [[String.uppercase_ascii con]] []

and mk_nullary ?(at = no) t con : exp =
  mk_case t [[String.uppercase_ascii con]] []

and mk_tup ?(at = no) es : exp =
  let ts = List.map (fun e -> e.note) es in
  let t = t_tup ts in
  tupE ~note:t es

and mk_str ?(at = no) tname fes : exp =
  let mk_field (fname, e) = let info = Xl.Atom.{def = tname; case = ""} in
                            (Xl.Atom.Atom fname $$ at % info, e)
  in
  strE ~note:(t_var tname) (List.map mk_field fes)


and mk_none ?(at = no) t : exp = optE t None
and mk_some ?(at = no) t e : exp = optE t (Some e)

let to_bool_exp b = BoolE b
let to_num_exp n = NumE n


(* Construct data structure *)

let il_of_list t f l = List.map f l |> listE t
let il_of_seq t f s = List.of_seq s |> il_of_list f t
let il_of_opt t f opt = Option.map f opt |> optE t
let il_of_tup t fel = List.map (fun (f, e) -> f e) fel |> tupE ~note:t

