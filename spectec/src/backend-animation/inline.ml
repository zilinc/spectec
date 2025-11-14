open Il.Ast
open Util.Error
open Util.Source
open Def
open Occur

module Ctx = struct
  type t = exp Map.t
  let empty = Map.empty
end

let rec inline_exp occ ctx exp : exp =
  exp

and inline_prems occ ctx prems : prem list =
  prems

let inline_clause cl : func_clause =
  let occ = occ_clause cl in
  let DefD (bs, args, exp, prems) = cl.it in
  let prems' = inline_prems occ Ctx.empty prems in
  let exp' = inline_exp occ Ctx.empty exp in
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
