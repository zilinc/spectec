open Il.Ast
open Util.Error
open Util.Source
open Def
open Occur

module Inline = Util.Lib.State (struct type t = Il.Subst.t end)

open Inline

let rec inline_exp occ exp : exp Inline.m =
  let* ctx = Inline.get () in
  Il.Subst.subst_exp ctx exp |> return

and inline_prem occ prem : prem list Inline.m =
  let* ctx = Inline.get () in
  match prem.it with
  | IfPr exp ->
    let* exp' = inline_exp occ exp in
    return [ IfPr exp' $> prem ]
  | LetPr (lhs, rhs, bs) ->
    (match lhs.it with
    | VarE v when Map.exists (fun v' o -> v.it = v' && o = Occur.Occ.LinOcc) occ ->
      let ctx' = Il.Subst.add_varid ctx v (Il.Subst.subst_exp ctx rhs) in
      let* () = put ctx' in
      return []
    | _ -> let* rhs' = inline_exp occ rhs in
           return [ LetPr (lhs, rhs', bs) $> prem ]
    )
  | ElsePr -> return [prem]
  | IterPr (prems, (iter, xes)) ->
    let* iter' = (match iter with
    | ListN (n, oi) -> let* n' = inline_exp occ n in return (ListN (n', oi))
    | _ -> return iter
    ) in
    let occ' = Occur.occ_prems (Fun.const true) `Once Occur.empty_occ prems in
    let prems', _ = run_state (inline_prems occ' prems) Il.Subst.empty in
    return [ IterPr (prems', (iter', xes)) $> prem ]
  | _ -> assert false

and inline_prems occ prems : prem list Inline.m =
  match prems with
  | [] -> return []
  | prem::prems ->
    let* oprem' = inline_prem  occ prem in
    let* prems' = inline_prems occ prems in
    return (oprem' @ prems')

let inline_clause cl : func_clause =
  let occ = occ_clause cl in
  let DefD (bs, args, exp, prems) = cl.it in
  let ((prems', exp'), _) = run_state (
    let* prems' = inline_prems occ prems in
    let* exp' = inline_exp occ exp in
    (prems', exp') |> return
  ) Il.Subst.empty in
  DefD (bs, args, exp', prems') $> cl


let inline_fdef fdef : func_def =
  let (id, ps, t, cls, partial) = fdef.it in
  let cls' = List.map inline_clause cls in
  (id, ps, t, cls', partial) $> fdef

let rec inline_dl_def dl : dl_def =
  match dl with
  | FuncDef fdef -> FuncDef (inline_fdef fdef)
  | RecDef  dls  -> RecDef (List.map inline_dl_def dls)
  | _ -> dl
