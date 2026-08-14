open Il.Ast
open Def
open Util.Source
open Il
open Il_util

(*
module S = Util.Lib.State(Subst)
open S
*)

(*
let subst_to_prems qs (subst : Subst.t) : prem list =
  let vsubst = subst.varid |> Subst.Map.to_list in
  let qs' = List.filter (fun q -> match q.it with
  | ExpP (v, t) -> 
  | 
  ) qs in
  List.map (fun (x, e) -> LetPr (qs', e, varE ~note:e.note x) $ no) vsubst

let au_clause qs ps (orid, cl) =
  let DefD (qs', args, exp, prems) = cl.it in
  let ps' = ps in
  let subst = Subst.empty in
  qs', ps', (orid, cl), subst

let au_clauses2 (orid1, cl1) (orid2, cl2) =
  let DefD (qs1, args1, exp1, prems1) = cl1.it in
  let DefD (qs2, args2, exp2, prems2) = cl2.it in
  let args1', args2' = au_args2 args1 args2 in
  let ps = _ in
  let qs = _ in
  let subst1, subst2 = _ in
  qs, ps, (orid1, cl1), (orid2, cl2), subst1, subst2

(*
   * [qs] the quantification list for [ps].
   * [ps] is the least common anti-instances of the patterns of the clauses in
     [cl_substs].
   * [cl_substs] is a list of pairs of (clause, subst) that have been anti-unified.
     The clauses are the same as original, but they will be applied by the substitutions
     later, when all clauses are anti-unified. The substitutions are cumulative.
   * [cls] are the clauses to be anti-unified with [p].
*)
let rec au_clauses' qs ps cl_substs cls : func_clause list = match cls with
| [] -> (* Apply the respective substitution to each clause. *)
  List.map (fun ((orid, cl), subst) ->
    let DefD (qs', args, exp, prems) = cl.it in
    let qs'' = qs in
    let args'' = args in
    let prems' = subst_to_prems qs' subst @ prems in
    (orid, DefD (qs'', args'', exp, prems') $ cl.at)
  ) cl_substs
| [cl] -> _
| cls -> _

let au_clauses cls : func_clause list = match cls with
| [] -> []
| [cl] -> [cl]
| cl1 :: cl2 :: cls -> let p12, cl1', cl2', subst1, subst2 = au_clauses2 cl1 cl2 in
                       au_clauses' p12 [(cl1', subst1); (cl2', subst2)] cls

let rec au_def def = match def with
| FuncDef fdef ->
  let fid, osubid, params, typ, cls, opartial = fdef.it in
  let cls' = au_clauses cls in
  FuncDef ((fid, osubid, params, typ, cls', opartial) $ fid.at)
| RecDef dl_defs -> RecDef (List.map au_def dl_defs)
| _ -> def

let au_script dl = List.map au_def dl
*)