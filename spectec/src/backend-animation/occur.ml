open Il.Ast
open Util.Error
open Util.Source
open Def

module Map = Map.Make(String)

type occ = int Map.t


let rec occ_exp occ exp : occ =
  match exp.it with
  | VarE v -> Map.update v.it (Option.fold ~none:(Some 1) ~some:(fun o -> Some (o+1))) occ
  | BoolE _ | NumE _ | TextE _ | OptE None -> occ
  | UnE (_, _, e) | ProjE (e, _) | CaseE (_, e) | UncaseE (e, _) | TheE e
  | DotE (e, _) | LiftE e | OptE (Some e) | LenE e | CvtE (e, _, _) | SubE (e, _, _)
  -> occ_exp occ e
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) | CompE (e1, e2)
  | MemE (e1, e2) | CatE (e1, e2) | IdxE (e1, e2)
  -> List.fold_left occ_exp occ [e1; e2]
  | SliceE (e1, e2, e3) -> List.fold_left occ_exp occ [e1; e2; e3]
  | TupE es | ListE es
  -> List.fold_left occ_exp occ es
  | StrE efs -> List.fold_left occ_expfield occ efs
  | UpdE (e1, p, e2) | ExtE (e1, p, e2)
  -> let occ1 = occ_exp occ e1 in
     let occ2 = occ_path occ1 p in
     occ_exp occ2 e2
  | CallE (_, args) -> List.fold_left occ_arg occ args
  (*
  | IterE of exp * iterexp       (* exp iter *)
  *)

and occ_expfield occ (atom, exp) : occ = occ_exp occ exp

and occ_path occ path : occ = match path.it with
  | RootP -> occ
  | IdxP (p, e) -> let occ' = occ_path occ p in occ_exp occ' e
  | SliceP (p, e1, e2) -> let occ' = occ_path occ p in
                          List.fold_left occ_exp occ' [e1; e2]
  | DotP (p, _) -> occ_path occ p

and occ_arg occ arg : occ = match arg.it with
  | ExpA e -> occ_exp occ e
  | _ -> occ


let occ_prem occ prem : occ =
  match prem.it with
  | IfPr exp -> occ_exp occ exp
  | LetPr(lhs, rhs, binds) -> occ_exp occ rhs
  | ElsePr -> occ
  | IterPr (prems, iterexp) -> todo "occ_prem: IterPr"
  | _ -> assert false

let rec occ_prems occ prems : occ =
  match prems with
  | [] -> occ
  | prem::prems' -> let occ'  = occ_prem  occ  prem   in
                    let occ'' = occ_prems occ' prems' in
                    occ''
