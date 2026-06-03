open Il.Ast
open Il.Walk
open Util.Error
open Util.Source
open Def
open Occur

module Inline = Util.Lib.State (struct type t = Il.Subst.t end)

open Inline

let simp : transformer = {
  transform_exp =
    (fun exp -> match exp.it with
    | IterE ({ it = VarE v; _ }, (List, xes)) when List.exists (fun (x, _) -> Il.Eq.eq_id x v) xes ->
      List.find (fun (x, _) -> Il.Eq.eq_id x v) xes |> snd
    | _ -> exp
    );
  transform_prem = id;
  transform_iterexp = id;
  transform_typ = id;
  transform_arg = id;
  transform_path = id;

  transform_var_id = id;
  transform_typ_id = id;
  transform_rel_id = id;
  transform_def_id = id;
  transform_gram_id = id;

  transform_types_of_exp = true
}


let rec inline_exp occ exp : exp Inline.m =
  let* ctx = Inline.get () in
  let exp' = Il.Subst.subst_exp ctx exp in
  let exp'' = transform_exp simp exp' in
  return exp''

and inline_prem occ prem : prem list Inline.m =
  let* ctx = Inline.get () in
  match prem.it with
  | IfPr exp ->
    let* exp' = inline_exp occ exp in
    return [ IfPr exp' $> prem ]
  | LetPr (qs, lhs, rhs) ->
    (match lhs.it with
    | VarE v when Map.exists (fun v' o -> v.it = v' && o = Occur.Occ.LinOcc) occ ->
      let ctx' = Il.Subst.add_varid ctx v (Il.Subst.subst_exp ctx rhs) in
      let* () = put ctx' in
      return []
    | _ -> let* rhs' = inline_exp occ rhs in
           return [ LetPr (qs, lhs, rhs') $> prem ]
    )
  | ElsePr -> return [prem]
  | IterPr (prem1, (iter, xes)) ->
    let* iter' = (match iter with
    | ListN (n, oi) -> let* n' = inline_exp occ n in return (ListN (n', oi))
    | _ -> return iter
    ) in
    let occ' = Occur.occ_prem (Fun.const true) `Once Occur.empty_occ prem1 in
    let* ctx = get () in
    let prems1', ctx_inner = run_state (inline_prem occ' prem1) ctx in
    (* If nested iterations, x <- x* may be removed because x is substituted.
       But in the outer binding list, x* <- x** should also be removed.
    *)
    let* xes' = Inline.foldlM (fun xes' (x, e) ->
      if Il.Subst.mem_varid ctx_inner x then
        (match e.it with
        | VarE v -> let e' = Il.Subst.find_varid ctx_inner x in
                    let* () = update (fun s -> Il.Subst.add_varid s v e') in
                    return xes'
        | _ -> assert false
        )
      else
        let* s = get() in
        let* e' = inline_exp occ e in
        return (xes' @ [(x, e')])
    ) [] xes in
    return (List.map (fun prem' -> IterPr (prem', (iter', xes')) $> prem) prems1')
  | _ -> assert false

and inline_prems occ prems : prem list Inline.m =
  match prems with
  | [] -> return []
  | prem::prems ->
    let* oprem' = inline_prem  occ prem in
    let* prems' = inline_prems occ prems in
    return (oprem' @ prems')

let inline_func_clause (fc: func_clause) : func_clause =
  let oid, cl = fc in
  let occ = occ_clause cl in
  let DefD (bs, args, exp, prems) = cl.it in
  let ((prems', exp'), _) = run_state (
    let* prems' = inline_prems occ prems in
    let* exp' = inline_exp occ exp in
    (prems', exp') |> return
  ) Il.Subst.empty in
  oid, DefD (bs, args, exp', prems') $ cl.at


let inline_fdef fdef : func_def =
  let (id, osubid, ps, t, cls, partial) = fdef.it in
  let cls' = List.map inline_func_clause cls in
  (id, osubid, ps, t, cls', partial) $> fdef

let rec inline_dl_def dl : dl_def =
  match dl with
  | FuncDef fdef -> FuncDef (inline_fdef fdef)
  | RecDef  dls  -> RecDef (List.map inline_dl_def dls)
  | _ -> dl
