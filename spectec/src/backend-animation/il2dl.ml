open Il.Ast
open Il.Print
open Il2al.Il2al_util
open Util
open Source
open Def
open Il_util
module H = State_v.Hints


(* Debug *)

let rec list_all_il_defs' lv (il: script) : unit =
  let indent n = String.make (2*n) ' ' in
  List.iter (fun def -> match def.it with
    | RecD defs -> print_endline "{"; list_all_il_defs' (lv+1) defs; print_endline "}"
    | TypD (id, _, _)    -> print_endline (indent lv ^ "typ | " ^ string_of_id id)
    | DecD (id, _, _, _) -> print_endline (indent lv ^ "dec | " ^ string_of_id id)
    | RelD (id, _, _, _) -> print_endline (indent lv ^ "rel | " ^ string_of_id id)
    | _ -> ()
  ) il
let list_all_il_defs (il: script) : unit = list_all_il_defs' 0 il

let rec list_all_dl_defs' lv dl : unit =
  let indent n = String.make (2*n) ' ' in
  List.iter (function
    | RecDef  defs -> print_endline "{"; list_all_dl_defs' (lv+1) defs; print_endline "}"
    | TypeDef tdef ->
      let id, _, _ = tdef.it in
      print_endline (indent lv ^ "type | " ^ string_of_id id)
    | FuncDef fdef ->
      let id, osubid, _, _, _, _ = fdef.it in
      print_endline (indent lv ^ "func | " ^ string_of_funcname id osubid)
  ) dl
let list_all_dl_defs (dl: dl_def list) : unit = list_all_dl_defs' 0 dl


(* Error *)

let error at msg = Util.Error.error at "IL -> DL" msg


(* Relations *)

(* TODO(zilinc): We currently do not consider dependent types in the signature of rules. *)

let il2dl_rule_clause rel_id rule : func_clause =
  let RuleD (id, binds, _, exp, prems) = rule.it in
  let has_animate_hint = H.is_a_rel rel_id.it in
  assert has_animate_hint;
  let mode_map = H.find_a_rel rel_id.it in
  let TupE es = exp.it in
  let lhs', rhs', _t1, t2 = Lib.List.fold_lefti (fun i (les, res, lts, rts) e ->
    let omode = H.IM.find_opt (i+1) mode_map in
    (match omode with
    | None     -> (les, res, lts, rts)
    | Some In  -> (les@[e], res, lts@[(VarE ("_" $ e.at) $> e, e.note)], rts)
    | Some Out -> (les, res@[e], lts, rts@[(VarE ("_" $ e.at) $> e, e.note)])
    )
  ) ([], [], [], []) es in
  let args = List.map (fun e -> ExpA e $ e.at) lhs' in
  let exp' = (match rhs' with
             | []  -> assert false
             | [e] -> e
             | _   -> TupE rhs' $$ exp.at % (TupT t2 $ exp.at)
             )
  in
  Some id, DefD (binds, args, exp', prems) $ rule.at


let il2dl_rule_def rule_name rel_id typ rules at : func_def =
  let osubid = if String.equal rule_name "" then None else Some (rule_name $ rel_id.at) in
  let func_clauses = List.map (il2dl_rule_clause rel_id) rules in
  let has_animate_hint = H.is_a_rel rel_id.it in
  assert has_animate_hint;
  let mode_map = H.find_a_rel rel_id.it in
  let TupT ts = typ.it in
  let lts, rts = Lib.List.fold_lefti (fun i (lts, rts) t ->
    let omode = H.IM.find_opt (i+1) mode_map in
    (match omode with
    | None     -> lts, rts
    | Some In  -> lts @ [t], rts
    | Some Out -> lts, rts @ [t]
    )
  ) ([], []) ts in
  let params = List.map (fun (e, t) -> ExpP ("_" $ t.at, t) $ t.at) lts in
  let rt = (match rts with
           | [] -> assert false
           | [(e,t)] -> t
           | ets -> TupT ets $ (over_region (List.map (fun x -> x.at) (List.map snd ets)))
           )
  in
  (rel_id, osubid, params, rt, func_clauses, None) $ at

(* Group reduction rules that have same rule name. *)
let rec group_rules : (id * typ * rule) list -> func_def list = function
  | [] -> []
  | h::t ->
    let (rel_id, typ, rule) = h in
    let rule_name = name_of_rule rule in
    let t1, t2 =
      List.partition (fun (_, _, rule) -> name_of_rule rule = rule_name) t in
    let rules = rule :: List.map (fun (rel_id', typ', rule') ->
      if rel_id = rel_id' then rule' else
        error rule'.at
        "this reduction rule uses a different relation compared to the previous rules"
    ) t1 in
    let at = rules |> List.map at |> over_region in
    let func_def = il2dl_rule_def rule_name rel_id typ rules at in

    func_def :: group_rules t2


(* Helper Definitions *)

let get_partial_func def : id option =
  let is_partial_hint hint = hint.hintid.it = "partial" in
  match def.it with
  | HintD { it = DecH (id, hints); _ } when List.exists is_partial_hint hints ->
    Some id
  | _ -> None


let il2dl_clause cl : func_clause =
  let DefD (binds, args, exp, prems) = cl.it in
  None, DefD (binds, args, exp, prems) $ cl.at


(* Entry *)


let rec il2dl (il: script) : dl_def list =
  let partial_funcs = List.filter_map get_partial_func il in
  List.concat_map (fun def ->
    match def.it with
    | TypD (id, params, insts) -> [TypeDef ((id, params, insts) $ def.at)]
    | DecD (id, params, typ, clauses) ->
      let partial = if List.mem id partial_funcs then Partial else Total in
      [FuncDef ((id, None, params, typ, List.map il2dl_clause clauses, Some partial) $ def.at)]
    | RelD (rel_id, _, typ, rules) ->
      let rules = List.map (fun rule -> (rel_id, typ, rule)) rules in
      let func_def = group_rules rules in
      List.map (fun r -> FuncDef r) func_def
    | RecD defs ->
      let defs' = il2dl defs in
      if List.is_empty defs' then [] else [RecDef defs']
    | _ -> []
  ) il
