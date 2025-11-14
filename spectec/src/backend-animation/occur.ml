open Il.Ast
open Util.Error
open Util.Source
open Def

module Map = Map.Make(String)

module Occ = struct
  type t = NoOcc | LinOcc | OmegaOcc

  let inc : t -> t = function
  | NoOcc -> LinOcc
  | _ -> OmegaOcc

  let to_string : t -> string = function
  | NoOcc  -> "𝟘"
  | LinOcc -> "𝟙"
  | OmegaOcc -> "ω"

end

type occ = Occ.t Map.t

let string_of_occ occ : string =
  Map.fold (fun k v acc ->
    acc ^ "\n" ^
    k ^ " ↦ " ^ Occ.to_string v
  ) occ ""


let inc_occ occ v : occ =
  Map.update v.it (Option.fold ~none:(Some Occ.LinOcc) ~some:(fun o -> Some (Occ.inc o))) occ
let many_occ occ v : occ =
  Map.update v.it (Fun.const (Some Occ.OmegaOcc)) occ
let empty_occ : occ = Map.empty


type mode = [ `Once | `Many ]

let rec occ_exp pred m occ exp : occ =
  match exp.it with
  | VarE v ->
    if pred v then
      match m with | `Once -> inc_occ occ v | `Many -> many_occ occ v
    else occ
  | BoolE _ | NumE _ | TextE _ | OptE None -> occ
  | UnE (_, _, e) | ProjE (e, _) | CaseE (_, e) | UncaseE (e, _) | TheE e
  | DotE (e, _) | LiftE e | OptE (Some e) | LenE e | CvtE (e, _, _) | SubE (e, _, _)
  -> occ_exp pred m occ e
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) | CompE (e1, e2)
  | MemE (e1, e2) | CatE (e1, e2) | IdxE (e1, e2)
  -> List.fold_left (occ_exp pred m) occ [e1; e2]
  | SliceE (e1, e2, e3) -> List.fold_left (occ_exp pred m) occ [e1; e2; e3]
  | TupE es | ListE es
  -> List.fold_left (occ_exp pred m) occ es
  | StrE efs -> List.fold_left (occ_expfield pred m) occ efs
  | UpdE (e1, p, e2) | ExtE (e1, p, e2)
  -> let occ1 = occ_exp pred m occ e1 in
     let occ2 = occ_path pred m occ1 p in
     occ_exp pred m occ2 e2
  | CallE (_, args) -> List.fold_left (occ_arg pred m) occ args
  | IterE (e, (iter, xes)) ->
    let occ1 = List.fold_left (fun o (x, e') ->
      match e'.it with
      | VarE v -> if pred v then many_occ o v else o
      | _ -> assert false
    ) occ xes in
    let occ2 = occ_exp (fun v -> pred v && not (List.mem v (List.map fst xes))) `Many occ1 e in
    occ2

and occ_expfield pred m occ (atom, exp) : occ = occ_exp pred m occ exp

and occ_path pred m occ path : occ = match path.it with
  | RootP -> occ
  | IdxP (p, e) -> let occ' = occ_path pred m occ p in occ_exp pred m occ' e
  | SliceP (p, e1, e2) -> let occ' = occ_path pred m occ p in
                          List.fold_left (occ_exp pred m) occ' [e1; e2]
  | DotP (p, _) -> occ_path pred m occ p

and occ_arg pred m occ arg : occ = match arg.it with
  | ExpA e -> occ_exp pred m occ e
  | _ -> occ


and occ_prem pred m occ prem : occ =
  match prem.it with
  | IfPr exp -> occ_exp pred m occ exp
  | LetPr(lhs, rhs, binds) -> occ_exp pred m occ rhs
  | ElsePr -> occ
  | IterPr (prems, (iter, xes)) ->
    let occ1 = List.fold_left (fun o (x, e') ->
      match e'.it with
      | VarE v -> if pred v then many_occ o v else o
      | _ -> assert false
    ) occ xes in
    let occ2 = occ_prems (fun v -> pred v && not (List.mem v (List.map fst xes))) `Many occ1 prems in
    occ2
  | _ -> assert false

and occ_prems pred m occ prems : occ =
  match prems with
  | [] -> occ
  | prem::prems' -> let occ'  = occ_prem  pred m occ  prem   in
                    let occ'' = occ_prems pred m occ' prems' in
                    occ''

let occ_clause cl : occ =
  let DefD (bs, args, exp, prems) = cl.it in
  let occ1 = occ_prems (Fun.const true) `Once empty_occ prems in
  let occ2 = occ_exp (Fun.const true) `Once occ1 exp in
  occ2

